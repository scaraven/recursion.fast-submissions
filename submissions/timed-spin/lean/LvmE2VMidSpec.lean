-- New for lvm2 S1 (E2-F, E2F-V; E2F-LEAD's review actions (2), (3)): the meaning of S2GF's split `E2` claims
-- (`splitE2_sound`, `isMultiaffine_splitE2`) and the pair-form middle-phase spec at `L₀ = 1` (`midSpecP_F₂`).
import LvmE2VMid
import LvmMPMidT
import LvmE2FPin
import LvmCertTInst
import LvmE2VMidSpecF

/-!
# S2GF's middle phases: the split claims and the spec

* `SumE2.Holds c col`: the `E2` claim on the words `col` of a `K` column: `Σ_k c_k·Σ_{n<2^v_k} eq(z_k, n)·col(o_k + n)
  = value` (the parts' blocks `⟨v_k, o_k⟩`).
* **`splitE2_sound`**: if the `E2` claim is false on a column, one of its two split claims (re, im) fails
  `StackClaim.Holds` on it (NOTE-FIELD Prop 7.1 through `wordClaimE2`, summed over the parts with their selectors);
  the parts' blocks aligned and inside the column, their points of the blocks' lengths.
* **`isMultiaffine_splitE2`**: both split weights are multiaffine on the stack (the PCS's premise).
* **`midSpecP_F₂`** (the S2GF twin of `midSpecP_T₂`): the pinned pair form of the middle phases at `L₀ = 1`:
  candidates `(q, recOf x q)` for `q ∈ candZ za`, shape `PinPost za`, every group `≤ εS`, lead
  `leadF₂ = 6·2^-131`; the good pair is `GoodTF` (`GkF`: S2GF's `KS` continuation rows). Its typed part is the
  coordinate split (`typedProgX`, QH3's `GbTX`, `THypX`), generic in the instance `Ti` (S2GF's is circuit-side).
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.VEq (BClaim VPlacement)
open Lvm.ASM (MidSpecP Pair εS)
open Finset

/-- **The `E2` claim on a column's words**: `Σ_k c_k·Σ_{n<2^v_k} eq(z_k, n)·col(o_k + n) = value`. -/
def SumE2.Holds (c : SumE2) (col : ℕ → K) : Prop :=
  (c.parts.map fun p ↦ p.1 *
    ∑ n ∈ range (2 ^ p.2.1.variableCount), eqAtF p.2.2 n * Lvm.Quad.C (col (p.2.1.index + n))).sum = c.value

/-- The parts' blocks are aligned, inside the `2^nu` words, and their points have the blocks' lengths. -/
def SumE2.Fits (nu : ℕ) (c : SumE2) : Prop :=
  ∀ p ∈ c.parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu ∧
    2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ nu

/-! ## The split through a coordinate of `E6` -/

section Split

open LeanVM.Protocol.EndToEnd (boolPoint)

/-- The `re` coordinate of `E6`, additive. -/
def reHom6 : E6 →+ E where
  toFun Y := Y.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `im` coordinate of `E6`, additive. -/
def imHom6 : E6 →+ E where
  toFun Y := Y.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `re` coordinate of `E2`, additive. -/
def reHom2 : E2 →+ K where
  toFun y := y.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `im` coordinate of `E2`, additive. -/
def imHom2 : E2 →+ K where
  toFun y := y.im
  map_zero' := rfl
  map_add' _ _ := rfl

theorem reHom6_apply (Y : E6) : reHom6 Y = Y.re := rfl

theorem imHom6_apply (Y : E6) : imHom6 Y = Y.im := rfl

theorem reHom2_apply (y : E2) : reHom2 y = y.re := rfl

theorem imHom2_apply (y : E2) : imHom2 y = y.im := rfl

theorem reHom6_C_mul (e : E) (Y : E6) : reHom6 (Lvm.Quad.C e * Y) = e * reHom6 Y := by
  show (Lvm.Quad.C e * Y).re = e * Y.re
  rw [mul_comm, Lvm.Quad.re_mul_C, mul_comm]

theorem imHom6_C_mul (e : E) (Y : E6) : imHom6 (Lvm.Quad.C e * Y) = e * imHom6 Y := by
  show (Lvm.Quad.C e * Y).im = e * Y.im
  rw [mul_comm, Lvm.Quad.im_mul_C, mul_comm]

theorem reHom2_mul_C (y : E2) (a : K) : reHom2 (y * Lvm.Quad.C a) = reHom2 y * a :=
  Lvm.Quad.re_mul_C y a

theorem imHom2_mul_C (y : E2) (a : K) : imHom2 (y * Lvm.Quad.C a) = imHom2 y * a :=
  Lvm.Quad.im_mul_C y a

theorem ofK_sum (s : Finset ℕ) (f : ℕ → K) : ofK (∑ n ∈ s, f n) = ∑ n ∈ s, ofK (f n) :=
  map_sum (algebraMap K E) f s

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- A weight that agrees on lists of length `n` with a multiaffine one is multiaffine. -/
theorem isMultiaffine_of_eqOn {n : ℕ} {Φ Ψ : List E → E} (h : IsMultiaffine n Ψ)
    (he : ∀ l : List E, l.length = n → Φ l = Ψ l) : IsMultiaffine n Φ := by
  intro l hl k hk X
  rw [he _ (by rw [List.length_set, hl]), he _ (by rw [List.length_set, hl]),
    he _ (by rw [List.length_set, hl])]
  exact h l hl k hk X

variable (π : E6 →+ E) (ρ : E2 →+ K) (hC : ∀ (e : E) (Y : E6), π (Lvm.Quad.C e * Y) = e * π Y)
  (hE : ∀ y, π (e2ToE6 y) = ofK (ρ y)) (hρ : ∀ y a, ρ (y * Lvm.Quad.C a) = ρ y * a)
include hC hE hρ

/-- **One part** of the split weight paired with the column: the coordinate of the part's `E2` sum. -/
theorem part_sum {nu : ℕ} (c : E2) (v off : ℕ) (z : List E2) (hz : z.length = v) (hal : 2 ^ v ∣ off)
    (hfit : off + 2 ^ v ≤ 2 ^ nu) (q : Column nu) :
    ∑ n ∈ range (2 ^ nu), π (e2ToE6 c * Lvm.Quad.C ((⟨v, off⟩ : VPlacement).eqAbove (boolPoint nu n)) *
        wordW z ((boolPoint nu n).take v)) * ofK (q.values.getD n 0) =
      ofK (ρ (c * ∑ n ∈ range (2 ^ v), eqAtF z n * Lvm.Quad.C (q.values.getD (off + n) 0))) := by
  subst hz
  have e1 : ∀ n, π (e2ToE6 c * Lvm.Quad.C ((⟨z.length, off⟩ : VPlacement).eqAbove (boolPoint nu n)) *
      wordW z ((boolPoint nu n).take z.length)) * ofK (q.values.getD n 0) =
        (⟨z.length, off⟩ : VPlacement).eqAbove (boolPoint nu n) *
          π (e2ToE6 c * wordW z ((boolPoint nu n).take z.length)) * ofK (q.values.getD n 0) := by
    intro n
    rw [show e2ToE6 c * Lvm.Quad.C ((⟨z.length, off⟩ : VPlacement).eqAbove (boolPoint nu n)) *
        wordW z ((boolPoint nu n).take z.length) =
      Lvm.Quad.C ((⟨z.length, off⟩ : VPlacement).eqAbove (boolPoint nu n)) *
        (e2ToE6 c * wordW z ((boolPoint nu n).take z.length)) by ring, hC]
  rw [sum_congr rfl fun n _ ↦ e1 n, ← Fin.sum_univ_eq_sum_range (fun n ↦
      (⟨z.length, off⟩ : VPlacement).eqAbove (boolPoint nu n) *
        π (e2ToE6 c * wordW z ((boolPoint nu n).take z.length)) * ofK (q.values.getD n 0)),
    Lvm.ASM.sum_block hal hfit (fun y ↦ π (e2ToE6 c * wordW z y)) q]
  rw [mul_sum, map_sum, ofK_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [wordW_boolPoint, ← map_mul, hE, ← mul_assoc, hρ, ofK_mul]

/-- **The split weight paired with the column** is the coordinate of the claim's `E2` sum. -/
theorem split_sum {nu : ℕ} (q : Column nu) : ∀ (parts : List (E2 × VPlacement × List E2)),
    (∀ p ∈ parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu ∧
      2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ nu) →
    ∑ n ∈ range (2 ^ nu), π (sumW6 parts (boolPoint nu n)) * ofK (q.values.getD n 0) =
      ofK (ρ (parts.map fun p ↦ p.1 *
        ∑ n ∈ range (2 ^ p.2.1.variableCount), eqAtF p.2.2 n *
          Lvm.Quad.C (q.values.getD (p.2.1.index + n) 0)).sum)
  | [], _ => by
    simp only [sumW6, List.map_nil, List.sum_nil, map_zero, zero_mul, sum_const_zero]
    rfl
  | (c, ⟨v, off⟩, z) :: ps, hc => by
    obtain ⟨hz, -, hal, hfit⟩ := hc _ (List.mem_cons_self ..)
    have ih := split_sum q ps fun p hp ↦ hc p (List.mem_cons_of_mem _ hp)
    simp only [sumW6, List.map_cons, List.sum_cons, map_add, add_mul, sum_add_distrib] at ih ⊢
    rw [ih, part_sum π ρ hC hE hρ c v off z hz hal hfit q]
    exact (map_add (algebraMap K E) _ _).symm

omit hρ in
/-- One part of the split weight is multiaffine on the stack. -/
theorem isMultiaffine_part {nu : ℕ} (c : E2) (v off : ℕ) (z : List E2) (hz : z.length = v)
    (hv : v ≤ nu) :
    IsMultiaffine nu fun x ↦ π (e2ToE6 c * Lvm.Quad.C ((⟨v, off⟩ : VPlacement).eqAbove x) *
      wordW z (x.take v)) := by
  subst hz
  have hw : IsMultiaffine z.length fun y ↦ π (e2ToE6 c * wordW z y) :=
    isMultiaffine_of_eqOn (isMultiaffine_sum_eqAt z.length (2 ^ z.length)
      fun n ↦ ofK (ρ (c * eqAtF z n))) fun y hy ↦ by
        rw [wordW_eq_sum z y hy, mul_sum, map_sum]
        refine sum_congr rfl fun n _ ↦ ?_
        rw [mul_left_comm, ← Lvm.Quad.C_eq_algebraMap, hC, ← map_mul, hE]
  have h := Lvm.ASM.isMultiaffine_onStack (n := nu)
    ⟨⟨z.length, off⟩, fun y ↦ π (e2ToE6 c * wordW z y), 0⟩ hv hw
  refine isMultiaffine_of_eqOn h fun x _ ↦ ?_
  show _ = (⟨z.length, off⟩ : VPlacement).eqAbove x * π (e2ToE6 c * wordW z (x.take z.length))
  rw [show e2ToE6 c * Lvm.Quad.C ((⟨z.length, off⟩ : VPlacement).eqAbove x) * wordW z (x.take z.length) =
      Lvm.Quad.C ((⟨z.length, off⟩ : VPlacement).eqAbove x) * (e2ToE6 c * wordW z (x.take z.length))
      by ring, hC]

omit hρ in
/-- **The split weight is multiaffine** on the stack. -/
theorem isMultiaffine_sumW6 {nu : ℕ} : ∀ (parts : List (E2 × VPlacement × List E2)),
    (∀ p ∈ parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu) →
    IsMultiaffine nu fun x ↦ π (sumW6 parts x)
  | [], _ => by
    simp only [sumW6, List.map_nil, List.sum_nil, map_zero]
    exact IsMultiaffine.zero
  | (c, ⟨v, off⟩, z) :: ps, hc => by
    obtain ⟨hz, hv⟩ := hc _ (List.mem_cons_self ..)
    have ih := isMultiaffine_sumW6 ps fun p hp ↦ hc p (List.mem_cons_of_mem _ hp)
    simp only [sumW6, List.map_cons, List.sum_cons, map_add] at ih ⊢
    exact (isMultiaffine_part π ρ hC hE c v off z hz hv).add ih

end Split

/-- **The split is sound**: a false `E2` claim makes one of its two split claims false on the column. -/
theorem splitE2_sound (nu : ℕ) (c : SumE2) (hc : c.Fits nu) (q : Column nu)
    (h : ¬ c.Holds (fun i ↦ q.values.getD i 0)) :
    ∃ b ∈ splitE2 nu c, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds nu b.onStack q := by
  by_contra hall
  apply h
  have hfit : ∀ p ∈ c.parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu ∧
      2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ nu := hc
  have hre := by_contra fun hn ↦ hall ⟨_, List.mem_cons_self .., hn⟩
  have him := by_contra fun hn ↦ hall ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hn⟩
  rw [Lvm.ASM.holds_onStack _ (dvd_zero _) (le_of_eq (zero_add _))] at hre him
  dsimp only at hre him
  simp only [zero_add] at hre him
  have ere := split_sum reHom6 reHom2 reHom6_C_mul (fun _ ↦ rfl) reHom2_mul_C q c.parts hfit
  have eim := split_sum imHom6 imHom2 imHom6_C_mul (fun _ ↦ rfl) imHom2_mul_C q c.parts hfit
  simp only [reHom6_apply, reHom2_apply] at ere
  simp only [imHom6_apply, imHom2_apply] at eim
  rw [ere] at hre
  rw [eim] at him
  exact QuadraticAlgebra.ext ((algebraMap K E).injective hre) ((algebraMap K E).injective him)

/-- **The split weights are multiaffine** on the stack. -/
theorem isMultiaffine_splitE2 (nu : ℕ) (c : SumE2) (hc : c.Fits nu) :
    ∀ b ∈ splitE2 nu c, IsMultiaffine nu b.onStack.1 := by
  have hfit : ∀ p ∈ c.parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu :=
    fun p hp ↦ ⟨(hc p hp).1, (hc p hp).2.1⟩
  intro b hb
  simp only [splitE2, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl
      (isMultiaffine_sumW6 reHom6 reHom2 reHom6_C_mul (fun _ ↦ rfl) c.parts hfit)
  · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl
      (isMultiaffine_sumW6 imHom6 imHom2 imHom6_C_mul (fun _ ↦ rfl) c.parts hfit)

/-- **The middle phases' lead at S2GF**: `6·2^-131`, so that the pin's `errE pinNum` in front still fits `εS = 7·2^-131`
(E2F-LEAD 2026-11-13; the first group, the typed phase's `τ`, `ω` with their follower, is far below it). -/
noncomputable abbrev leadF₂ : ENNReal := 6 * (2 : ENNReal)⁻¹ ^ 131

/-- **The `KS` half of the good pair on the continuation rows `rows`**: the tape's relation and `KS`'s. -/
def GkFR (rows : List ℕ) (x : List UInt8) (p : Pair) : Prop :=
  Lvm.NS.TapeG x p.1 ∧
  Lvm.KG.KSRel 13 9 Lvm.NS.ksY2 rows (Lvm.NS.colM p.1) (Lvm.NS.ksCol p.1) (Lvm.NS.msgM p.2) (Lvm.NS.msgX p.1)

/-- **The `KS` half of the good pair at S2GF** (`GkS` with S2GF's continuation rows `contRowsF`, from the S2GF
trace's 4,295 sponge blocks, instead of `contRows P20`'s 4,447): the tape's relation and `KS`'s. -/
def GkF (x : List UInt8) (p : Pair) : Prop :=
  GkFR contRowsF x p

/-- **The good pair at S2GF** (`GoodT`'s shape on the coordinate split: `GbTX` and `GkF`). -/
def GoodTF (Ti : Lvm.Typed.TInst) (H : Lvm.Typed.THypX Ti) : Lvm.ASM.GoodRel :=
  fun x qm qr ↦ Lvm.Typed.GbTX Ti H x (qm, qr) ∧ GkF x (qm, qr)

/-- **The pinned pair form of S2GF's middle phases** (`midSpecP_T₂`'s twin, `L₀ = 1`): for every pin `za`, the
middle phases from `PinPost za` end in `OpenPostRG` over the pairs of `candZ za`, every group `≤ εS`, lead `leadF₂`. -/
theorem midSpecP_F₂ (Ti : Lvm.Typed.TInst) (H : Lvm.Typed.THypX Ti)
    (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E) :
    MidSpecP (midF₂ Ti) (fun x h ↦ (fun q ↦ ((q, recOf x q) : Pair)) '' Lvm.E2F.candZ za h)
      (Lvm.E2F.PinPost za) (Lvm.Shape.Good₂ (GoodTF Ti H)) εS leadF₂ := by
  exact midSpecP_F₂_core (fun nu c hc q h ↦ splitE2_sound nu c hc q h)
    (fun nu c hc ↦ isMultiaffine_splitE2 nu c hc) H recOf za GkF (fun _ _ ht hk ↦ ⟨ht, hk⟩)

/-- The `E2` front's assembled claims: at most `100` per commitment, so `assembleF₂` adds at most `200`. -/
theorem length_assembleF₂ (x : List UInt8) (a : Lvm.ASM.OpenClaims) (k : KgOutF) (hk : KgRetF k) :
    (assembleF₂ x a k).2.length + (assembleF₂ x a k).1.length ≤ a.1.length + a.2.length + 200 := by
  have hlen := length_claimsF x k hk
  have l1 : (assembleSF (Lvm.VEq.pubX x) k).1.length ≤ 100 := by
    rw [assembleSF_eq, List.length_map]; exact (List.length_filter_le _ _).trans hlen
  have l2 : (assembleSF (Lvm.VEq.pubX x) k).2.length ≤ 100 := by
    rw [assembleSF_eq, List.length_map]; exact (List.length_filter_le _ _).trans hlen
  have e2 : (assembleF₂ x a k).2.length = (a.2 ++ (assembleSF (Lvm.VEq.pubX x) k).2).length := by
    simp only [assembleF₂, Lvm.Shape.onStackZs]
    split_ifs <;> simp only [List.length_map]
  rw [e2]
  simp only [assembleF₂, List.length_append]
  omega

/-- **The middle phases' claims are fewer than `2^40`** (strict, as `midSpecPin_of`'s `hlen` needs; roll 11's
`retOK_midT₂_len` is `≤`). -/
theorem retOK_midF₂_len (Ti : Lvm.Typed.TInst) (H : Lvm.Typed.THypX Ti) (x : List UInt8) :
    LeanVM.Protocol.EndToEnd.Sound.RetOK (fun cl : Lvm.ASM.OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40)
      (midF₂ Ti x) :=
  ((retOK_typedProgX_len H _).bind fun a ha ↦ (retOK_kgProgF _ _).bind fun k hk ↦
      LeanVM.Protocol.EndToEnd.Sound.RetOK.ret
        ((length_assembleF₂ x a k hk).trans_lt (by norm_num at ha ⊢; omega)) :
    LeanVM.Protocol.EndToEnd.Sound.RetOK (fun cl : Lvm.ASM.OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40)
      (midF₂ Ti x))

/-- **The middle phases commit nothing and ask no proof of work of the language** (`NoCG`). -/
theorem cg_midF₂ (Ti : Lvm.Typed.TInst) (x : List UInt8) : Lvm.M3.NoCG (midF₂ Ti x) :=
  Lvm.M3.NoCG.bind (cg_typedProgX _ _) fun _ ↦ Lvm.M3.NoCG.bind (cg_kgProgF _ _) fun _ ↦
    Lvm.M3.cg_ret _

end Lvm.E2V
