-- New for lvm6 Y1 (2026-11-23): the typed phases at `E` as WP S's frozen phase statement `Stmt.typedSpecE`
-- (`Lvm6StmtPhase`): CD's windows on the one stack (CD-circuit.md §0: `C_main` = the whole stack `⟨25, 0⟩`,
-- `C_rec` = slot 33, `⟨19, 33·2^19⟩`), the claims on the stack, and `DoomSpec` from `Lvm6.Ty.typedSpecE`.
import Lvm6TySpec
import Lvm6TyNoCommit
import Lvm6StmtPhase

/-!
# `Stmt.typedSpecE` from `typedSpecE`

* **The windows**: a stack `q` gives the pair `toPair q = (q on [0, 2^25), q on [33·2^19, 34·2^19))`; a `C_main`
  claim is a stack claim as it is (`holds_main`), a `C_rec` claim is placed on its window by `recClaim`
  (`eq_above` of `⟨19, 33·2^19⟩`, `holds_rec`).
* **`TyInst6`**: an instance of the typed phases at these windows (CD's `Ti`, the public words, the incoming
  accumulator, and the static facts `TypedSpecEStmt` asks); **`typedPhase6 sh i`**: `typedProgE` then the seven claims
  on the stack, in FORMAT6 §6.4's order (the two `C_rec` claims first); it rejects at a shape with `M ≠ 25`.
  **`TGood6 i q`**: `TGoodE` on `toPair q` and `AccOkE`.
* **`typedSpec6 : Stmt.typedSpecE typedPhase6 TGood6`**: for a candidate map that is a subsingleton on `G`, glue over
  the candidate set (`Lvm.M3.Spec.glue`); on one set, `typedSpecE` at the image pairs with `L₀ = 1`, `εI`,
  follower `0` (`errsE_at`); its `firstWord` precondition is met on a history with one more commitment in front,
  which a program with no query cannot tell apart (`Spec.shiftNQ`).
* **`typedPhase6_noCommit`**: `Stmt.noCommit` of the phase.
-/

set_option autoImplicit false

namespace Lvm6.Ty

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.VerifierProgram
open LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm6.Mb Finset
open scoped ENNReal

/-! ## Programs with no query -/

section NoQuery

variable {α β : Type}

/-- **`p` asks no opening.** -/
def NoQuery : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoQuery (k x)
  | .sample k => ∀ c, NoQuery (k c)
  | .grind _ k => NoQuery k
  | .commit _ _ k => NoQuery k
  | .query _ _ _ => False

theorem NoQuery.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoQuery p)
    (hf : ∀ a, NoQuery (f a)) : NoQuery (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact hp.elim

theorem NoQuery.after {p q : VerifierProgram α} (hp : NoQuery p) {l : List Ev}
    (h : p.after l = some q) : NoQuery q := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact hp.elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

/-- The runs of a program with no query do not depend on the history before it. -/
theorem NoQuery.reach {p : VerifierProgram α} (hp : NoQuery p) {h₀ h₁ l : List Ev} (hr : p.Reach h₀ l) :
    p.Reach h₁ l := by
  induction hr with
  | nil => exact .nil
  | read x _ ha ih => exact .read x ih ha
  | sample c _ ha ih => exact .sample c ih ha
  | grind _ ha ih => exact .grind ih ha
  | commit word _ ha hw ih => exact .commit word ih ha hw
  | query _ ha _ _ => exact ((hp.after ha) : False).elim

theorem nq_bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoQuery p)
    (hf : ∀ a, NoQuery (f a)) : NoQuery (p >>= f) := NoQuery.bind hp hf

theorem nq_readScalar : NoQuery (VerifierProgram.readScalar) := fun _ ↦ trivial

theorem nq_sampleChallenge : NoQuery (VerifierProgram.sampleChallenge) := fun _ ↦ trivial

theorem nq_require (c : Prop) {_ : Decidable c} : NoQuery (VerifierProgram.require c) := by
  unfold VerifierProgram.require; split <;> trivial

theorem nq_sampleChallenges : ∀ n, NoQuery (VerifierProgram.sampleChallenges n)
  | 0 => trivial
  | n + 1 => nq_bind nq_sampleChallenge fun _ ↦ nq_bind (nq_sampleChallenges n) fun _ ↦ trivial

end NoQuery

theorem nq_e2Read : NoQuery e2Read := nq_bind nq_readScalar fun _ ↦ trivial

theorem nq_e2Reads : ∀ n, NoQuery (e2Reads n)
  | 0 => trivial
  | n + 1 => nq_bind nq_e2Read fun _ ↦ nq_bind (nq_e2Reads n) fun _ ↦ trivial

theorem nq_e2Sample (g : ℕ) : NoQuery (e2Sample g) :=
  nq_bind nq_readScalar fun _ ↦ nq_bind nq_sampleChallenge fun _ ↦ nq_bind (nq_require _) fun _ ↦ trivial

theorem nq_e2Samples (g : ℕ) : ∀ n, NoQuery (e2Samples g n)
  | 0 => trivial
  | n + 1 => nq_bind (nq_e2Sample g) fun _ ↦ nq_bind (nq_e2Samples g n) fun _ ↦ trivial

theorem nq_e2SampleN (g : ℕ) : ∀ n, NoQuery (e2SampleN g n)
  | 0 => trivial
  | n + 1 => nq_bind nq_readScalar fun _ ↦ nq_bind nq_sampleChallenge fun _ ↦ nq_bind (nq_require _) fun _ ↦
      nq_bind (nq_sampleChallenges n) fun _ ↦ trivial

theorem nq_roundPolyE2 (count : ℕ) (claim : E2) (mode : Option E2) : NoQuery (roundPolyE2 count claim mode) := by
  cases mode with
  | none => exact nq_bind nq_e2Read fun _ ↦ nq_bind (nq_e2Reads _) fun _ ↦ trivial
  | some r => exact nq_bind (nq_e2Reads _) fun _ ↦ trivial

theorem nq_sumcheckE2 (g : ℕ) (count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    NoQuery (sumcheckE2 g claim count modes)
  | [], _ => trivial
  | m :: ms, claim => nq_bind (nq_roundPolyE2 count claim m) fun _ ↦ nq_bind (nq_e2Sample g) fun _ ↦
      nq_bind (nq_sumcheckE2 g count ms _) fun _ ↦ trivial

theorem nq_gkrStepG (gy step : ℕ) (s : GkrStateG) : NoQuery (gkrStepG gy step s) :=
  nq_bind (nq_e2Sample _) fun _ ↦ nq_bind (nq_sumcheckE2 _ _ _ _) fun _ ↦ nq_bind (nq_e2Reads _) fun _ ↦
    nq_bind (nq_e2Reads _) fun _ ↦ nq_bind (nq_e2Reads _) fun _ ↦ nq_bind (nq_require _) fun _ ↦
      nq_bind (nq_e2SampleN _ _) fun _ ↦ trivial

theorem nq_gkrLayersG : ∀ (n : ℕ) (s : GkrStateG), NoQuery (gkrLayersG n s)
  | 0, _ => trivial
  | 1, s => nq_gkrStepG _ _ s
  | n + 2, s => by
    unfold gkrLayersG
    split
    · exact nq_bind (nq_gkrStepG _ _ s) fun s' ↦ nq_gkrLayersG (n + 1) s'
    · exact nq_bind (nq_gkrStepG _ _ s) fun s' ↦ nq_gkrLayersG n s'

theorem nq_miniBusLProg6 (L : Lvm.M3.Lay) (tabs : List Lvm.M3.Tab) (μ : ℕ) : NoQuery (miniBusLProg6 L tabs μ) :=
  nq_bind (nq_bind (nq_e2SampleN _ _) fun _ ↦
    nq_bind (nq_bind nq_e2Read fun _ ↦ nq_bind nq_e2Read fun _ ↦ nq_bind (nq_gkrLayersG _ _) fun _ ↦ trivial)
      fun _ ↦ nq_bind (nq_require _) fun _ ↦ trivial) fun _ ↦ trivial

theorem nq_accShape (n : ℕ) (P : List E2 → List E2 → E2 → Prop) (dec : ∀ a b c, Decidable (P a b c)) :
    NoQuery (e2Samples gKappa selBitsE >>= fun κ ↦ e2Reads n >>= fun hs ↦ e2Sample gT >>= fun t ↦
      @VerifierProgram.require (P κ hs t) (dec κ hs t)) :=
  nq_bind (nq_e2Samples _ _) fun _ ↦ nq_bind (nq_e2Reads n) fun _ ↦ nq_bind (nq_e2Sample _) fun _ ↦ nq_require _

theorem nq_typedProgE (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → Lvm.FK) (acc : List E2 × E2) :
    NoQuery (typedProgE Ti L pw acc) := by
  unfold typedProgE
  refine nq_bind (nq_bind (nq_e2Samples _ _) fun _ ↦ nq_bind (nq_sumcheckE2 _ _ _ _) fun _ ↦
    nq_bind (nq_e2Reads _) fun _ ↦ nq_bind (nq_require _) fun _ ↦ trivial) fun _ ↦ ?_
  refine nq_bind (nq_bind (nq_e2Sample _) fun _ ↦ nq_bind (nq_sumcheckE2 _ _ _ _) fun _ ↦
    nq_bind (nq_e2Reads _) fun _ ↦ nq_bind (nq_e2Reads _) fun _ ↦ nq_bind (nq_require _) fun _ ↦ trivial) fun _ ↦ ?_
  refine nq_bind (nq_bind (nq_sumcheckE2 _ _ _ _) fun _ ↦ nq_bind nq_e2Read fun _ ↦
    nq_bind (nq_require _) fun _ ↦ trivial) fun _ ↦ ?_
  exact nq_bind (nq_accShape (phiVarsE + 1) _ _) fun _ ↦ nq_bind (nq_miniBusLProg6 _ _ _) fun _ ↦ trivial

/-! ## A specification moved to another history -/

section Shift

variable {α : Type} {p : VerifierProgram α} {Pre Pre' : List Ev → Prop} {Post Post' : α → List Ev → Prop}
  {εmax L T : ℝ≥0∞}

/-- **A specification of a program with no query, read after another history** `f h₀`: its runs are the same. -/
noncomputable def Spec.shiftNQ (hq : NoQuery p) (f : List Ev → List Ev) (S : Spec p Pre Post εmax L T)
    (hpre : ∀ h, Pre' h → Pre (f h)) (hpost : ∀ a h₀ l, Post a (f h₀ ++ l) → Post' a (h₀ ++ l)) :
    Spec p Pre' Post' εmax L T where
  D h₀ l := S.D (f h₀) l
  V h₀ l := S.V (f h₀) l
  le_one h₀ l := S.le_one _ _
  start_D h₀ hp := S.start_D _ (hpre h₀ hp)
  start_V h₀ hp := S.start_V _ (hpre h₀ hp)
  read x hr ha hD := S.read x (hq.reach hr) ha hD
  grind hr ha hD := S.grind (hq.reach hr) ha hD
  commit word hr ha hw hD := S.commit word (hq.reach hr) ha hw hD
  sample hr ha := S.sample (hq.reach hr) ha
  query _ ha _ := ((hq.after ha) : False).elim
  moveEnd hr ha hm hD := S.moveEnd (hq.reach hr) ha hm hD
  retEnd hr ha hD := S.retEnd (hq.reach hr) ha hD
  retDoom hr ha hD := S.retDoom (hq.reach hr) ha hD
  post hr ha hD := hpost _ _ _ (S.post (hq.reach hr) ha hD)
  bound hr hl he hD := S.bound (hq.reach hr) hl he hD

end Shift

/-! ## The windows (CD-circuit.md §0) -/

/-- The commitments' sizes: `C_main` the whole stack (`2^25` words), `C_rec` one slot (`2^19`). -/
abbrev L6 : Lvm.M3.Lay := ⟨25, 19⟩

/-- `C_rec`'s offset on the stack: slot 33. -/
abbrev recOff : ℕ := 33 * 2 ^ 19

/-- The column of the first `2^n` words of `f`. -/
def colOf (n : ℕ) (f : ℕ → K) : Column n := ⟨Vector.ofFn fun x ↦ f x.val⟩

/-- **The pair of windows of a stack**: `C_main` = words `[0, 2^25)`, `C_rec` = words `[33·2^19, 34·2^19)`. -/
def toPair (q : Lvm6.Stack) : Column 25 × Column 19 := (colOf 25 q, colOf 19 fun n ↦ q (recOff + n))

/-- A `C_rec` claim placed on its window. -/
def recClaim (c : ClaimE) : Lvm6.StackClaim6 := (fun X ↦ eqAboveG ⟨19, recOff⟩ X * c.1 (X.take 19), c.2)

/-- **The typed claims on the stack**: the `C_rec` claims (relayout point, `σ′`) on their window, then the `C_main`
claims (committed block, `KS`, the mini-bus's three); FORMAT6-T §3's order. -/
def claimsOnStack (out : OpenClaimsE) : List Lvm6.StackClaim6 := out.1.map recClaim ++ out.2

theorem boolPt_eq_bitsF : ∀ (μ x : ℕ), Lvm6.boolPt μ x = (bitsF x μ : List E2)
  | 0, _ => rfl
  | μ + 1, x => by
    have h : Lvm6.boolPt (μ + 1) x = (if x % 2 = 1 then 1 else 0) :: Lvm6.boolPt μ (x / 2) := by
      simp only [Lvm6.boolPt, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp [Nat.testBit_zero]
      · refine List.map_congr_left fun i _ ↦ ?_
        simp [Function.comp, Nat.testBit_succ]
    rw [h, boolPt_eq_bitsF μ (x / 2)]
    rfl

theorem colOf_getD {n : ℕ} (f : ℕ → K) {x : ℕ} (hx : x < 2 ^ n) : (colOf n f).values.getD x 0 = f x := by
  simp [colOf, Vector.getD, Array.getD, hx]

/-- A `C_main` claim is a stack claim. -/
theorem holds_main (c : ClaimE) (q : Lvm6.Stack) :
    Lvm6.StackClaim6.Holds 25 c q ↔ ClaimE.Holds 25 c (toPair q).1 := by
  unfold Lvm6.StackClaim6.Holds ClaimE.Holds
  refine Eq.congr_left (Finset.sum_congr rfl fun x _ ↦ ?_)
  rw [boolPt_eq_bitsF, toPair, colOf_getD q x.isLt]

theorem bitsF_add_mul : ∀ (m n a : ℕ), (bitsF (n + 2 ^ m * a) m : List E2) = bitsF n m
  | 0, _, _ => rfl
  | m + 1, n, a => by
    have e : 2 ^ (m + 1) * a = 2 * (2 ^ m * a) := by ring
    have h1 : (n + 2 ^ (m + 1) * a) % 2 = n % 2 := by rw [e]; omega
    have h2 : (n + 2 ^ (m + 1) * a) / 2 = n / 2 + 2 ^ m * a := by rw [e]; omega
    rw [bitsF, bitsF, h1, h2, bitsF_add_mul m (n / 2) a]

/-- A `C_rec` claim holds on its window iff it holds on `C_rec`. -/
theorem holds_rec (c : ClaimE) (q : Lvm6.Stack) :
    Lvm6.StackClaim6.Holds 25 (recClaim c) q ↔ ClaimE.Holds 19 c (toPair q).2 := by
  unfold Lvm6.StackClaim6.Holds ClaimE.Holds recClaim toPair
  refine Eq.congr_left ?_
  have hw : ∀ x : ℕ, x < 2 ^ 25 → eqAboveG ⟨19, recOff⟩ (bitsF x 25 : List E2) * c.1 ((bitsF x 25 : List E2).take 19) =
      if x / 2 ^ 19 = 33 then c.1 (bitsF x 19) else 0 := by
    intro x hx
    rw [eqAboveG_eq, bitsF_drop _ _ _ (by norm_num), bitsF_take _ _ _ (by norm_num),
      Nat.mul_div_cancel _ (Nat.two_pow_pos 19),
      eqAtF_bitsF_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hx)) (by norm_num)]
    split_ifs with h1 h2 h2 <;> simp_all
  show (∑ x : Fin (2 ^ 25), eqAboveG ⟨19, recOff⟩ (Lvm6.boolPt 25 x) * c.1 ((Lvm6.boolPt 25 x).take 19) *
      algebraMap K E2 (q x)) = ∑ x : Fin (2 ^ 19), c.1 (bitsF x 19) *
        algebraMap K E2 ((colOf 19 fun n ↦ q (recOff + n)).values.getD x 0)
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqAboveG ⟨19, recOff⟩ (Lvm6.boolPt 25 x) *
    c.1 ((Lvm6.boolPt 25 x).take 19) * algebraMap K E2 (q x)) (2 ^ 25),
    Fin.sum_univ_eq_sum_range (fun x ↦ c.1 (bitsF x 19) * algebraMap K E2 ((colOf 19 fun n ↦ q (recOff + n)).values.getD x 0))
      (2 ^ 19)]
  rw [Finset.sum_congr rfl fun x hx ↦ by
    rw [boolPt_eq_bitsF, hw x (Finset.mem_range.mp hx), ite_mul, zero_mul]]
  rw [← Finset.sum_filter]
  have hr : recOff = 17301504 := rfl
  have h19 : (2 : ℕ) ^ 19 = 524288 := by norm_num
  have h25 : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  refine Finset.sum_nbij' (fun x ↦ x - recOff) (fun n ↦ recOff + n) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    omega
  · intro n _
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hx' : x = (x - recOff) + 2 ^ 19 * 33 := by omega
    rw [colOf_getD _ (by omega), Nat.add_sub_cancel' (by omega)]
    conv_lhs => rw [hx', bitsF_add_mul]
    rw [← hx']

/-! ## The instance and the phase -/

/-- **A typed instance at CD's windows**: the program's instance, the public words, the incoming accumulator and the
static facts `TypedSpecEStmt` asks. -/
structure TyInst6 where
  /-- The typed instance. -/
  Ti : TInst6
  /-- The public words. -/
  pw : ℕ → Lvm.FK
  /-- The incoming accumulator. -/
  acc : List E2 × E2
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L6.μ
  ok : Ti.Ok
  maps : Ti.MapsFit L6
  accLen : acc.1.length = phiVarsE
  sc : Lvm.M3.AllSc Ti.mbT
  lay : Lvm.M3.LayOk L6 Ti.mbT
  keys : Lvm.M3.KeysOk Ti.mbT
  fix : Lvm.M3.FixOk Ti.mbT
  lin : mbLinB6 Ti.mbT = true
  μBus : (Lvm.M3.inst L6 Ti.mbT hτ).μBus = miniDepth

/-- **The typed phase on the stack** (FORMAT6 §6.4): `typedProgE`, then the seven claims on the stack; it rejects at
a shape whose stack is not `2^25` words. -/
noncomputable def typedPhase6 (sh : Lvm6.Shape) (i : TyInst6) : VerifierProgram (List Lvm6.StackClaim6) :=
  if sh.M = 25 then typedProgE i.Ti L6 i.pw i.acc >>= fun out ↦ pure (claimsOnStack out) else VerifierProgram.fail

/-- **The typed relation on a stack**: `TGoodE` on its windows, and the incoming accumulator. -/
def TGood6 (i : TyInst6) (q : Lvm6.Stack) : Prop := TGoodE i.Ti L6 i.hτ i.pw (toPair q) ∧ AccOkE i.Ti i.acc

theorem εI_eq : εI = Lvm6.εI := rfl

/-- The phase on one candidate set (a subsingleton). -/
noncomputable def typedSpecOne (i : TyInst6) (R : Lvm6.Stack → Prop) (S : Set Lvm6.Stack) (hS : S.Subsingleton) :
    Spec (typedProgE i.Ti L6 i.pw i.acc >>= fun out ↦ pure (claimsOnStack out))
      (fun h ↦ Doomed (fun _ ↦ S) (fun q ↦ TGood6 i q ∧ R q) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun q ↦ (∀ c ∈ out, Lvm6.StackClaim6.Holds 25 c q) ∧ R q) h) εI 0 0 := by
  classical
  let S' : Set (Column 25 × Column 19) := toPair '' S
  let R' : Column 25 × Column 19 → Prop := fun p ↦ ∃ q ∈ S, toPair q = p ∧ R q
  have hfin : S'.Finite := (hS.image toPair).finite
  have hcard : S'.ncard ≤ 1 := by
    have := hfin.to_subtype
    exact (Set.ncard_le_one_iff_subsingleton).mpr (hS.image toPair)
  let f : List Ev → List Ev := fun h ↦ Ev.commit 0 0 default :: h
  have spec := Classical.choice (typedSpecE i.Ti L6 i.pw i.acc i.hτ (fun _ ↦ S') R' (L₀ := 1) (εmax := εI) (T := 0)
    (fun _ ↦ True) i.ok i.maps rfl i.accLen i.sc i.lay i.keys i.fix i.lin i.μBus (fun _ _ _ ↦ rfl)
    (fun _ ↦ hfin) (fun _ ↦ hcard) εI_lt_one errsE_at)
  refine (Spec.shiftNQ (nq_typedProgE _ _ _ _) f spec (Pre' := fun h ↦ Doomed (fun _ ↦ S) (fun q ↦ TGood6 i q ∧ R q) h)
    (Post' := fun out h ↦ Doomed (fun _ ↦ S') (fun p ↦ TClaimsHoldE L6 out p ∧ R' p) h) ?_ ?_).bind' fun out ↦ ?_
  · intro h hD
    refine ⟨trivial, ⟨default, rfl⟩, fun p hp hA ↦ ?_⟩
    obtain ⟨q', hq'S, hq'p, hRq'⟩ := hA.2.1
    obtain ⟨q, hqS, rfl⟩ := hp
    exact hD q' hq'S ⟨⟨by rw [hq'p]; exact hA.1, hA.2.2⟩, hRq'⟩
  · intro a h₀ l hP
    exact hP
  · refine (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun q ↦ (∀ c ∈ out, Lvm6.StackClaim6.Holds 25 c q) ∧ R q) h)
      (claimsOnStack out)).mono (fun h hD q hqS hq ↦ ?_) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
    refine hD (toPair q) ⟨q, hqS, rfl⟩ ⟨⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩, q, hqS, rfl, hq.2⟩
    · exact (holds_rec c q).mp (hq.1 _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
    · exact (holds_main c q).mp (hq.1 _ (List.mem_append_right _ hc))

/-- **T4 at WP S's statement**: `Stmt.typedSpecE` for the typed phase at CD's windows. -/
theorem typedSpec6 : Lvm6.Stmt.typedSpecE typedPhase6 TGood6 := by
  classical
  intro sh i C R G hCG hsub
  by_cases hM : sh.M = 25
  · have hp : typedPhase6 sh i = (typedProgE i.Ti L6 i.pw i.acc >>= fun out ↦ pure (claimsOnStack out)) := by
      unfold typedPhase6; rw [if_pos hM]
    rw [hp, hM]
    let F : ∀ S : Set Lvm6.Stack, Spec (typedProgE i.Ti L6 i.pw i.acc >>= fun out ↦ pure (claimsOnStack out))
        (fun h ↦ S.Subsingleton ∧ Doomed (fun _ ↦ S) (fun q ↦ TGood6 i q ∧ R q) h)
        (fun out h ↦ Doomed (fun _ ↦ S) (fun q ↦ (∀ c ∈ out, Lvm6.StackClaim6.Holds 25 c q) ∧ R q) h) εI 0 0 :=
      fun S ↦ if hS : S.Subsingleton then (typedSpecOne i R S hS).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl
        le_rfl le_rfl
      else specOfFalseG fun _ hp ↦ hS hp.1
    exact ⟨((Lvm.M3.Spec.glue C G hCG F).mono (fun h hp ↦ ⟨hp.1, hsub h hp.1, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl
      le_rfl le_rfl)⟩
  · have hp : typedPhase6 sh i = VerifierProgram.fail := by unfold typedPhase6; rw [if_neg hM]
    rw [hp]
    exact ⟨Spec.fail⟩

/-- **The typed phase commits nothing** (`Stmt.noCommit`). -/
theorem typedPhase6_noCommit (sh : Lvm6.Shape) (i : TyInst6) : Lvm6.Stmt.noCommit (typedPhase6 sh i) := by
  intro h₀ l hl
  refine VerifierProgram.NoCommit.reach_commits ?_ hl
  unfold typedPhase6
  split
  · exact nc_bind (nc_typedProgE _ _ _ _) fun _ ↦ trivial
  · trivial

end Lvm6.Ty
