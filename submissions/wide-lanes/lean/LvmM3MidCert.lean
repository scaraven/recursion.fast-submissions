-- new for lvm (WP-9b): the bus/table phases at WP-14's candidate pairs (`LvmCertS.candPairs`,
-- `RootShape`), from `midBusTableSpecB` and WP-14's `Spec.frame` (LvmCertSFrame).
import LvmCertS
import LvmM3Inst
import LvmSpineSeams
import LvmM3Mid
import LvmCertSFrame

-- ===== merged from `LvmM3MidStack` (GOLF module merge: `LvmM3MidStack.lean` is now a stub importing `LvmM3MidCert`) =====
section
-- new for lvm (WP-9b): the instance's stack of the two commitments, and a committed column's claim
-- as a claim on its commitment (WP-9's `LayOk`, `liftAt`/`readWith_liftAt` of `LvmM3Inst`, the
-- slice lemmas of WP-2's `LvmCpMultilinear`).

/-!
# The stack of `C_main` and `C_rec`, and committed columns as blocks of them

* **`stackOf L qm qr`**: the instance's stack of `nuMain + 1` variables, `C_main`'s word `qm` in the
  low half and `C_rec`'s `qr` at `2^nuMain`, zero above it.
* **`column_stackOf`**: under `LayOk`, committed column `(rec, off)` of table `j`, read off
  `stackOf qm qr`, is the block of `2^τ` cells of its commitment at `off` (`comBlock`).
* **`colClaim_iff`**: so a claim on it holds iff the block's extension at the claim's point is the
  value; **`eval_comBlock`**: that extension is the commitment's at `z ++ bits(off / 2^τ)`, the
  stack point of the placement `⟨τ, off⟩` (the native `BlockClaim.point ⟨τ, off⟩ z v`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

variable (L : Lay)

/-- **The stack of the two commitments**: `qm` in the low half, `qr` at `2^nuMain`, zero above. -/
def stackOf (qm : Column L.nuMain) (qr : Column L.nuRec) : Column L.μ :=
  ⟨Vector.ofFn fun x ↦ if h : x.val < 2 ^ L.nuMain then qm.values[x.val] else
    if h' : x.val - 2 ^ L.nuMain < 2 ^ L.nuRec then qr.values[x.val - 2 ^ L.nuMain] else 0⟩

/-- Cell `n` of commitment `rec` (`C_rec` if `rec`, else `C_main`; `0` past it). -/
def comCell (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (n : ℕ) : K :=
  if rec then (if h : n < 2 ^ L.nuRec then qr.values[n] else 0)
  else (if h : n < 2 ^ L.nuMain then qm.values[n] else 0)

/-- The block of `2^τ` cells of commitment `rec` from `off`. -/
def comBlock (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (τ off : ℕ) : Column τ :=
  ⟨Vector.ofFn fun x ↦ comCell L qm qr rec (off + x.val)⟩

/-- A cell of the stack: `C_main`'s below `2^nuMain`, `C_rec`'s above. -/
theorem stackOf_getElem (qm : Column L.nuMain) (qr : Column L.nuRec) (n : ℕ) (hn : n < 2 ^ L.μ) :
    (stackOf L qm qr).values[n] = if n < 2 ^ L.nuMain then comCell L qm qr false n
      else comCell L qm qr true (n - 2 ^ L.nuMain) := by
  simp only [stackOf, Vector.getElem_ofFn, comCell]
  by_cases h : n < 2 ^ L.nuMain
  · simp [h]
  · simp [h]

variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A committed column read off the stack of the commitments is its block** (under `LayOk`). -/
theorem column_stackOf (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (j : Fin tabs.length) (i : Fin (tabs.get j).w) {rec : Bool} {off : ℕ}
    (hcol : (tabs.get j).cols[i.val]? = some (.com rec off)) :
    (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ = comBlock L qm qr rec (tabs.get j).τ off := by
  have hal := hlay (tabs.get j) (List.get_mem _ _) i.val i.isLt
  unfold Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, hnu⟩ := hal
  have hder : (inst L tabs hτ).derived ⟨j, i⟩ = none := by
    simp only [inst, Tab.fixedOf, hcol, Option.map_none]
  have hτμ : (tabs.get j).τ ≤ L.μ := hτ _ (List.get_mem _ _)
  have hso : stackOff L (tabs.get j) i.val = off + if rec then 2 ^ L.nuMain else 0 := by
    simp only [stackOff, hcol]
  have hτm : (tabs.get j).τ ≤ L.nuMain := by
    have h1 : 2 ^ (tabs.get j).τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain) := by (clear * - hfit hso; omega)
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    cases rec
    · simpa using h2
    · exact le_trans (by simpa using h2) hnu
  have hdvd' : 2 ^ (tabs.get j).τ ∣ stackOff L (tabs.get j) i.val := by
    rw [hso]
    refine Nat.dvd_add hdvd ?_
    split
    · exact Nat.pow_dvd_pow 2 hτm
    · exact Nat.dvd_zero _
  have hfit' : stackOff L (tabs.get j) i.val + 2 ^ (tabs.get j).τ ≤ 2 ^ L.μ := by
    rw [hso, Lay.μ, pow_succ]
    have : 2 ^ L.nuRec ≤ 2 ^ L.nuMain := Nat.pow_le_pow_right (by norm_num) hnu
    cases rec <;> simp at hfit ⊢ <;> (clear * - hfit this; omega)
  have hsel : (selOf L (tabs.get j) hτμ i.val).val = stackOff L (tabs.get j) i.val / 2 ^ (tabs.get j).τ := by
    simp only [selOf, dif_pos (And.intro hdvd' hfit')]
  have hread := readWith_liftAt (fun c : (inst L tabs hτ).ColumnId ↦ hτ _ (List.get_mem _ c.1))
    (fun c ↦ selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2) (stackOf L qm qr) ⟨j, i⟩
  have hcolv : (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ =
      (inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩ := by
    unfold M3Instance.column; rw [hder]; rfl
  rw [hcolv]
  show (⟨((inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩).values⟩ : Column _) =
    ⟨(comBlock L qm qr rec (tabs.get j).τ off).values⟩
  congr 1
  change (Layout.readWith (fun c : (inst L tabs hτ).ColumnId ↦ liftAt (hτ _ (List.get_mem _ c.1))
    (selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2)) (stackOf L qm qr) ⟨j, i⟩).values = _
  rw [hread]
  apply Vector.ext
  intro x hx
  have hxl : x < 2 ^ (tabs.get j).τ := hx
  rw [slice_getElem_nat _ _ hxl, Vector.getElem_cast, stackOf_getElem]
  simp only [comBlock, Vector.getElem_ofFn]
  have key : ∀ n, n = off + x + (if rec then 2 ^ L.nuMain else 0) →
      (if n < 2 ^ L.nuMain then comCell L qm qr false n else comCell L qm qr true (n - 2 ^ L.nuMain)) =
        comCell L qm qr rec (off + x) := by
    intro n hn
    subst hn
    cases rec
    · have h1 : off + x < 2 ^ L.nuMain := by simp only [Bool.false_eq_true, ite_false] at hfit; (clear * - hτ hτμ hxl hfit; omega)
      simp [h1]
    · have h2 : ¬ off + x + 2 ^ L.nuMain < 2 ^ L.nuMain := by (clear * - hτ hτμ; omega)
      simp [h2]
  refine key _ ?_
  show x + 2 ^ (tabs.get j).τ * (selOf L (tabs.get j) hτμ i.val).val = _
  rw [hsel, Nat.mul_div_cancel' hdvd', hso]; (clear * - hτ hτμ; omega)

/-- **A committed column's claim on the stack of the commitments is a claim on its block.** -/
theorem colClaim_iff (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (c : ColumnClaim (inst L tabs hτ)) {rec : Bool} {off : ℕ}
    (hcol : (tabs.get c.col.1).cols[c.col.2.val]? = some (ColSrc.com rec off)) :
    c.Holds (stackOf L qm qr) ↔
      eval₂Mle (comBlock L qm qr rec (tabs.get c.col.1).τ off).values (algebraMap K E) c.point =
        c.value := by
  unfold ColumnClaim.Holds
  rw [column_stackOf L tabs hτ hlay qm qr c.col.1 c.col.2 hcol]

/-- **A block's extension is its commitment's at the placement's stack point**: for a block of
`2^τ` cells at `off = 2^τ·s` of a commitment of `ν ≥ τ` variables, its extension at `z` is the
commitment's at `z ++ bits(s)`. -/
theorem eval_block {ν τ : ℕ} (h : τ ≤ ν) (w : CMlPolynomialEval K ν) (s : ℕ)
    (hs : s < 2 ^ (ν - τ)) (z : Vector E τ) :
    eval₂Mle (Vector.ofFn fun x : Fin (2 ^ τ) ↦ w[2 ^ τ * s + x.val]'(by
        have := x.isLt
        calc 2 ^ τ * s + x.val < 2 ^ τ * s + 2 ^ τ := by omega
          _ = 2 ^ τ * (s + 1) := by ring
          _ ≤ 2 ^ τ * 2 ^ (ν - τ) := Nat.mul_le_mul_left _ hs
          _ = 2 ^ ν := by rw [← pow_add, Nat.add_sub_cancel' h])) (algebraMap K E) z =
      eval₂Mle w (algebraMap K E)
        (Vector.cast (Nat.add_sub_cancel' h) (z ++ (boolVec ⟨s, hs⟩ : Vector E (ν - τ)))) := by
  have e := Nat.add_sub_cancel' h
  have key := eval₂Mle_cast (algebraMap K E) e (Vector.cast (congrArg (2 ^ ·) e.symm) w)
    (z ++ (boolVec ⟨s, hs⟩ : Vector E (ν - τ)))
  rw [Vector.cast_cast, Vector.cast_rfl] at key
  rw [key, eval₂Mle, eval₂Mle, evalMle_append_boolVec, ← slice_map]
  congr 2
  apply Vector.ext
  intro x hx
  rw [slice_getElem_nat _ _ hx, Vector.getElem_ofFn, Vector.getElem_cast]
  simp only [Nat.add_comm (2 ^ τ * s) x]

/-- **`C_main`'s block**: the extension of a committed `C_main` column (block at `off`, aligned,
inside `C_main`) at `z` is `C_main`'s at the placement's stack point. -/
theorem eval_comBlock_main (qm : Column L.nuMain) (qr : Column L.nuRec) {τ off : ℕ}
    (hτ' : τ ≤ L.nuMain) (hdvd : 2 ^ τ ∣ off) (hfit : off + 2 ^ τ ≤ 2 ^ L.nuMain) (z : Vector E τ) :
    eval₂Mle (comBlock L qm qr false τ off).values (algebraMap K E) z =
      eval₂Mle qm.values (algebraMap K E) (Vector.cast (Nat.add_sub_cancel' hτ')
        (z ++ (boolVec ⟨off / 2 ^ τ, by
          have := Nat.div_mul_cancel hdvd
          have h2 : 2 ^ L.nuMain = 2 ^ τ * 2 ^ (L.nuMain - τ) := by rw [← pow_add, Nat.add_sub_cancel' hτ']
          have hp : 0 < 2 ^ τ := Nat.two_pow_pos _
          rw [h2] at hfit
          have : 2 ^ τ * (off / 2 ^ τ + 1) ≤ 2 ^ τ * 2 ^ (L.nuMain - τ) := by
            rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]; exact hfit
          exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left this hp)⟩ : Vector E (L.nuMain - τ)))) := by
  rw [← eval_block hτ' qm.values]
  congr 1
  apply Vector.ext
  intro x hx
  simp only [comBlock, comCell, Vector.getElem_ofFn, Bool.false_eq_true, ite_false,
    Nat.mul_div_cancel' hdvd]
  rw [dif_pos (by (clear * - hfit hx; omega))]

/-- **`C_rec`'s block**, as `eval_comBlock_main`. -/
theorem eval_comBlock_rec (qm : Column L.nuMain) (qr : Column L.nuRec) {τ off : ℕ}
    (hτ' : τ ≤ L.nuRec) (hdvd : 2 ^ τ ∣ off) (hfit : off + 2 ^ τ ≤ 2 ^ L.nuRec) (z : Vector E τ) :
    eval₂Mle (comBlock L qm qr true τ off).values (algebraMap K E) z =
      eval₂Mle qr.values (algebraMap K E) (Vector.cast (Nat.add_sub_cancel' hτ')
        (z ++ (boolVec ⟨off / 2 ^ τ, by
          have h2 : 2 ^ L.nuRec = 2 ^ τ * 2 ^ (L.nuRec - τ) := by rw [← pow_add, Nat.add_sub_cancel' hτ']
          have hp : 0 < 2 ^ τ := Nat.two_pow_pos _
          rw [h2] at hfit
          have : 2 ^ τ * (off / 2 ^ τ + 1) ≤ 2 ^ τ * 2 ^ (L.nuRec - τ) := by
            rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]; exact hfit
          exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left this hp)⟩ : Vector E (L.nuRec - τ)))) := by
  rw [← eval_block hτ' qr.values]
  congr 1
  apply Vector.ext
  intro x hx
  simp only [comBlock, comCell, Vector.getElem_ofFn, ite_true, Nat.mul_div_cancel' hdvd]
  rw [dif_pos (by (clear * - hfit hx; omega))]

end Lvm.M3
end
-- ===== end of `LvmM3MidStack` =====

-- ===== merged from `LvmM3MidPost` (GOLF module merge: `LvmM3MidPost.lean` is now a stub importing `LvmM3MidCert`) =====
section
-- new for lvm (WP-9b): `midBusTableSpec` with a post on the returned claims alone (WP-14's next
-- phase, `kgSpec`, carries a predicate of the claims inside one `Doomed`), per stack and per
-- commitment block; and the phases 2–3 program commits nothing and asks no proof of work (the
-- leaves adapted from WP-14's `LvmCertSNo` on lvm/ASM 220a1249, `nc_*`/`ng_*`, as one predicate).

/-!
# The bus/table phases' post on the claims, and their structure

* **`CommittedHolds tabs q c`**: the table phase's claim `c` (a global column, a point, a value),
  decoded with `colLoc`, holds of the stack `q` when it is on a committed column (claims on fixed
  columns are vacuous); **`BlockHolds L tabs qm qr c`**: the same on the commitments' block
  (`comBlock`, the native `BlockClaim.point ⟨τ, off⟩`); `committedHolds_iff_block` under `LayOk`.
* **`midBusTableSpec'`**: Post `Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds tabs (stk p) c) ∧ R p)`;
  **`midBusTableSpecB`**: candidates are pairs `(qm, qr)`, `stk = stackOf`, Post with `BlockHolds`.
* **`noCG_lbusTableCheckProg`**: `lbusTableCheckProg` commits nothing and asks no proof of work
  (`NoCommit ∧ NoGrind`, LvmCertSFrame), so `RootShape`-like facts of the history carry through
  (`Spec.frame` with `NoCommit.reach_commits`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## No commitment, no proof of work -/

section NoCG

open VerifierProgram

variable {α β : Type}

/-- `p` commits nothing and asks no proof of work. -/
def NoCG (p : VerifierProgram α) : Prop := p.NoCommit ∧ p.NoGrind

theorem NoCG.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCG p)
    (hf : ∀ a, NoCG (f a)) : NoCG (p.bind f) :=
  ⟨NoCommit.bind hp.1 fun a ↦ (hf a).1, NoGrind.bind hp.2 fun a ↦ (hf a).2⟩

theorem cg_ret (a : α) : NoCG (VerifierProgram.ret a) := ⟨trivial, trivial⟩
theorem cg_sample : NoCG (sampleChallenge : VerifierProgram E) := ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
theorem cg_readScalar : NoCG (readScalar : VerifierProgram E) := ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
theorem cg_require (c : Prop) [Decidable c] : NoCG (require c) := by
  unfold require; split <;> exact ⟨trivial, trivial⟩

theorem cg_readScalars : ∀ n, NoCG (readScalars n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_readScalars n) fun _ ↦ cg_ret _

theorem cg_sampleChallenges : ∀ n, NoCG (sampleChallenges n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_sampleChallenges n) fun _ ↦ cg_ret _

theorem cg_roundPoly (c : ℕ) (t : E) : ∀ e, NoCG (Verifier.sumcheckRoundPoly c t e)
  | none => by
    unfold Verifier.sumcheckRoundPoly
    exact NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦ cg_ret _
  | some _ => by
    unfold Verifier.sumcheckRoundPoly
    exact NoCG.bind (cg_readScalars _) fun _ ↦ cg_ret _

theorem cg_sumcheck (count : ℕ) : ∀ (es : List (Option E)) (claim : E),
    NoCG (Verifier.sumcheck claim count es)
  | [], _ => cg_ret _
  | e :: es, claim => by
    unfold Verifier.sumcheck
    refine NoCG.bind (cg_roundPoly _ _ e) fun msg ↦ NoCG.bind cg_sample fun ch ↦ ?_
    exact NoCG.bind (cg_sumcheck count es _) fun r ↦ cg_ret _

theorem cg_gkrStep (step : ℕ) (s : Verifier.GkrState) : NoCG (Verifier.gkrStep step s) := by
  unfold Verifier.gkrStep
  refine NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨x, claim⟩ := r
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
      NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_ret _

theorem cg_gkrLayers : ∀ (n : ℕ) (s : Verifier.GkrState), NoCG (Verifier.gkrLayers n s)
  | 0, _ => cg_ret _
  | 1, s => by
    unfold Verifier.gkrLayers
    exact NoCG.bind (cg_gkrStep 1 s) fun _ ↦ cg_ret _
  | n + 2, s => by
    unfold Verifier.gkrLayers
    split
    · exact NoCG.bind (cg_gkrStep 1 s) fun s' ↦ cg_gkrLayers (n + 1) s'
    · exact NoCG.bind (cg_gkrStep 2 s) fun s' ↦ cg_gkrLayers n s'

theorem cg_verifyGkr (depth : ℕ) : NoCG (Verifier.verifyGkrGrandProducts depth) := by
  unfold Verifier.verifyGkrGrandProducts
  exact NoCG.bind cg_readScalar fun _ ↦ NoCG.bind cg_readScalar fun _ ↦
    NoCG.bind (cg_gkrLayers _ _) fun _ ↦ cg_ret _

theorem cg_abProg : NoCG abProg :=
  NoCG.bind (cg_sampleChallenges 4) fun _ ↦ NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_lvmBusProg (μ : ℕ) : NoCG (lvmBusProg μ) :=
  NoCG.bind cg_abProg fun _ ↦ NoCG.bind (cg_verifyGkr μ) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_tableTermsClaims (tables : List Verifier.Table) (cps fps pt : List E) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      NoCG (Verifier.tableTermsClaims tables cps fps pt rows cursor final claims)
  | [], _, _, _ => cg_ret _
  | (table, height, forms, weight) :: rest, cursor, final, claims => by
    unfold Verifier.tableTermsClaims
    exact NoCG.bind (cg_readScalars _) fun _ ↦ cg_tableTermsClaims tables cps fps pt rest _ _ _

theorem cg_tablePhaseClaims (tables : List Verifier.Table) (layout : Verifier.Layout)
    (bus : Verifier.BusResult) : NoCG (Verifier.tablePhaseClaims tables layout bus) := by
  unfold Verifier.tablePhaseClaims Verifier.tableSumcheckClaims
  refine NoCG.bind cg_sample fun _ ↦ NoCG.bind (NoCG.bind (cg_sumcheck _ _ _) fun r ↦ ?_)
    fun _ ↦ cg_ret _
  obtain ⟨ch, claim⟩ := r
  refine NoCG.bind (cg_tableTermsClaims _ _ _ _ _ _ _ _) fun r ↦ ?_
  obtain ⟨final, cl⟩ := r
  exact NoCG.bind (cg_require _) fun _ ↦ cg_ret _

/-- **V_S phases 2–3 commit nothing and ask no proof of work.** -/
theorem noCG_lbusTableCheckProg (tabs : List Tab) (μ : ℕ) : NoCG (lbusTableCheckProg tabs μ) :=
  NoCG.bind (NoCG.bind (cg_lvmBusProg μ) fun _ ↦ cg_tablePhaseClaims _ _ _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ cg_ret _

end NoCG

/-! ## The claims' post -/

section Post

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A table-phase claim on a committed column holds of the stack `q`**: decoded with `colLoc` to
column `i` of table `j`, a committed column, its extension at the claim's point is the value
(claims on fixed columns, and claims that do not decode, are vacuous). -/
def CommittedHolds (q : Column L.μ) (c : Verifier.ColumnClaim) : Prop :=
  ∀ j i (hj : j < tabs.length) (hi : i < (tabs.get ⟨j, hj⟩).w) (rec : Bool) (off : ℕ),
    colLoc tabs c.column = some (j, i) → (tabs.get ⟨j, hj⟩).cols[i]? = some (.com rec off) →
    eval₂Mle ((inst L tabs hτ).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩).values (algebraMap K E)
      (vecOf _ c.point) = c.value

/-- **A table-phase claim on a committed column holds of its commitment's block**: as
`CommittedHolds`, on `comBlock qm qr rec τ off` (the native `BlockClaim.point ⟨τ, off⟩ pt v` on
`C_rec` if `rec`, else `C_main`). -/
def BlockHolds (qm : Column L.nuMain) (qr : Column L.nuRec) (c : Verifier.ColumnClaim) : Prop :=
  ∀ j i (hj : j < tabs.length) (rec : Bool) (off : ℕ),
    colLoc tabs c.column = some (j, i) → (tabs.get ⟨j, hj⟩).cols[i]? = some (.com rec off) →
    eval₂Mle (comBlock L qm qr rec (tabs.get ⟨j, hj⟩).τ off).values (algebraMap K E)
      (vecOf _ c.point) = c.value

/-- Under `LayOk`, a claim holds of the stack of the commitments iff it holds of its block. -/
theorem committedHolds_iff_block (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (c : Verifier.ColumnClaim) :
    CommittedHolds L tabs hτ (stackOf L qm qr) c ↔ BlockHolds L tabs qm qr c := by
  constructor
  · intro h j i hj rec off hl hcol
    have hi : i < (tabs.get ⟨j, hj⟩).w := (List.getElem?_eq_some_iff.mp hcol).1
    have := h j i hj hi rec off hl hcol
    rwa [column_stackOf L tabs hτ hlay qm qr ⟨j, hj⟩ ⟨i, hi⟩ hcol] at this
  · intro h j i hj hi rec off hl hcol
    rw [column_stackOf L tabs hτ hlay qm qr ⟨j, hj⟩ ⟨i, hi⟩ hcol]
    exact h j i hj rec off hl hcol

theorem vecOf_toList {n : ℕ} (v : Vector E n) : vecOf n v.toList = v := by
  apply Vector.ext; intro i hi
  simp [vecOf, hi]

/-- A table-phase output's committed claims hold when the program's claims (all of them, on the
committed columns) do. -/
theorem holds_of_committed {cl : List Verifier.ColumnClaim} {q : Column L.μ}
    {tout : Unit × TableOut (inst L tabs hτ)}
    (hmem : ∀ c ∈ tout.2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ cl)
    (h : ∀ c ∈ cl, CommittedHolds L tabs hτ q c) :
    ∀ c ∈ tout.2.columns.toList, (inst L tabs hτ).derived c.col = none → c.Holds q := by
  intro c hc hder
  have hloc := colLoc_colOfL L tabs hτ c.col
  have hi' : c.col.2.val < (tabs.get c.col.1).w := c.col.2.isLt
  obtain ⟨rec, off, hcol⟩ : ∃ rec off, (tabs.get c.col.1).cols[c.col.2.val]? =
      some (.com rec off) := by
    have hsome : ((tabs.get c.col.1).cols[c.col.2.val]?).isSome := by
      rw [List.getElem?_eq_getElem hi']; rfl
    obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.mp hsome
    cases src with
    | com rec off => exact ⟨rec, off, hsrc⟩
    | fix f ev =>
      exfalso
      have : (inst L tabs hτ).derived c.col ≠ none := by
        simp only [inst, Tab.fixedOf, hsrc, Option.map_some]; simp
      exact this hder
  have := h _ (hmem c hc) c.col.1.val c.col.2.val c.col.1.isLt hi' rec off hloc hcol
  unfold ColumnClaim.Holds
  rw [vecOf_toList] at this
  exact this

variable {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ}
  {εmax : ℝ≥0∞}

/-- **`midBusTableSpec` with a post on the claims alone**: every candidate meeting `R` fails a
committed claim the phases return. -/
noncomputable def midBusTableSpec' (hsc : AllSc tabs) (hkey : KeysOk tabs)
    (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs) (G : List Ev → Prop)
    (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L tabs hτ) () (stk p) ∧ R p) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds L tabs hτ (stk p) c) ∧ R p) h)
      εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  (midBusTableSpec L tabs hτ hsc C stk R hkey hw hfix G hCG hf hc hμ hab he4 hT hlam he3 hTf
    hxi).mono (fun _ h ↦ h)
    (fun cl h ⟨tout, hD, hmem, _⟩ p hp ⟨hall, hR⟩ ↦
      hD p hp ⟨holds_of_committed L tabs hτ hmem hall, hR⟩) le_rfl le_rfl le_rfl

/-- **The same on the commitments' blocks** (candidates `(qm, qr)`, the stack `stackOf`): every
candidate pair meeting `R` fails a committed claim on its `C_main`/`C_rec` block, under `LayOk`. -/
noncomputable def midBusTableSpecB (C : List Ev → Set (Column L.nuMain × Column L.nuRec))
    (R : Column L.nuMain × Column L.nuRec → Prop) (hlay : LayOk L tabs)
    (hsc : AllSc tabs) (hkey : KeysOk tabs)
    (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs) (G : List Ev → Prop)
    (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L tabs hτ) () (stackOf L p.1 p.2) ∧ R p) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, BlockHolds L tabs p.1 p.2 c) ∧ R p) h)
      εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  (midBusTableSpec' L tabs hτ C (fun p ↦ stackOf L p.1 p.2) R hsc hkey hw hfix G hCG hf hc hμ hab
    he4 hT hlam he3 hTf hxi).mono (fun _ h ↦ h)
    (fun cl h hD p hp ⟨hall, hR⟩ ↦ hD p hp ⟨fun c hc ↦
      (committedHolds_iff_block L tabs hτ hlay p.1 p.2 c).mpr (hall c hc), hR⟩) le_rfl le_rfl le_rfl

end Post

end Lvm.M3
end
-- ===== end of `LvmM3MidPost` =====

/-!
# The bus/table phases on WP-14's candidate pairs

* `wordOf_commits_append`, `candPairs_append`: the candidate pairs read only the first two
  commitments, so they do not move once two are made (the `hCG` of `midBusTableSpec*`, with
  `G h := 2 ≤ (commits h).length`);
* `rootShape_two`, `rootShape_firstWord`, `rootShape_append` (after a run that commits nothing);
* **`midBusTableSpecS`**: V_S phases 2–3 from `RootShape ∧ Doomed candPairs (M3Holds ∘ stackOf ∧ R)`
  to `Doomed candPairs ((∀ c ∈ cl, BlockHolds …) ∧ R) ∧ RootShape`, the stack of a pair being
  `stackOf ⟨26, 19⟩ qm qr` (`μ = 27`, `C_rec` at `2^26`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck LeanVM.Protocol.Whir.Sound CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-- A commitment's word does not change once it is made. -/
theorem wordOf_commits_append (h₀ l : List Ev) {i : ℕ} (hi : i < (commits h₀).length) :
    wordOf (commits (h₀ ++ l)) i = wordOf (commits h₀) i := by
  simp only [wordOf, commits_append, List.getElem?_append_left hi]

/-- **The candidate pairs do not move once two commitments are made.** -/
theorem candPairs_append (h₀ l : List Ev) (h2 : 2 ≤ (commits h₀).length) :
    Lvm.ASM.candPairs (h₀ ++ l) = Lvm.ASM.candPairs h₀ := by
  simp only [Lvm.ASM.candPairs, wordOf_commits_append h₀ l (show 0 < (commits h₀).length by omega),
    wordOf_commits_append h₀ l (show 1 < (commits h₀).length by omega)]

theorem rootShape_two {h : List Ev} (hr : Lvm.ASM.RootShape h) : 2 ≤ (commits h).length := by
  obtain ⟨Wm, Wr, hc, -⟩ := hr; rw [hc]; simp

theorem rootShape_firstWord {h : List Ev} (hr : Lvm.ASM.RootShape h) : ∃ W, firstWord h = some W := by
  obtain ⟨Wm, Wr, hc, -⟩ := hr
  exact ⟨Wm, by simp [firstWord, hc]⟩

/-- `RootShape` survives a run that commits nothing. -/
theorem rootShape_append {h₀ l : List Ev} (hl : commits l = []) (hr : Lvm.ASM.RootShape h₀) :
    Lvm.ASM.RootShape (h₀ ++ l) := by
  obtain ⟨Wm, Wr, hc, hw⟩ := hr
  exact ⟨Wm, Wr, by rw [commits_append, hl, List.append_nil, hc], hw⟩

/-- WP-14's commitment sizes as a layout: `C_main` 2^23 words (lvm2 roll 8, B1: physical ν = 23; S2: 2^24; v1:
2^26), `C_rec` 2^19 (the name is v1's). -/
abbrev lay26 : Lay := ⟨23, 19⟩

variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ lay26.μ) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **V_S phases 2–3 on WP-14's candidate pairs**: from `RootShape` and the root doom of
`M3Holds ∘ stackOf ∧ R` to the doom of the returned claims on the pairs' blocks, with `R`, and
`RootShape`. `hc` is the unique-decoding bound on the candidate pairs (WP-14's
`candPairs_ncard_le_one` for `L₀ = 1`). -/
noncomputable def midBusTableSpecS (R : Column CMain.nu20 × Column 19 → Prop) (hlay : LayOk lay26 tabs)
    (hsc : AllSc tabs) (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs)
    (hc : ∀ h, (Lvm.ASM.candPairs h).ncard ≤ L₀)
    (hμ : (inst lay26 tabs hτ).μBus ≠ 0) (hab : abError (inst lay26 tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst lay26 tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst lay26 tabs hτ).μBus)
      (fun h ↦ Lvm.ASM.RootShape h ∧ Doomed Lvm.ASM.candPairs
        (fun p ↦ M3Holds (inst lay26 tabs hτ) () (stackOf lay26 p.1 p.2) ∧ R p) h)
      (fun cl h ↦ Doomed Lvm.ASM.candPairs
        (fun p ↦ (∀ c ∈ cl, BlockHolds lay26 tabs p.1 p.2 c) ∧ R p) h ∧ Lvm.ASM.RootShape h)
      εmax (abError (inst lay26 tabs hτ) L₀ + 0) T :=
  ((midBusTableSpecB lay26 tabs hτ Lvm.ASM.candPairs R hlay hsc hkey hw hfix
      (fun h ↦ 2 ≤ (commits h).length) (fun h₀ l h2 ↦ candPairs_append h₀ l h2)
      (fun _ ↦ Set.toFinite _) hc hμ hab he4 hT hlam he3 hTf hxi).frame Lvm.ASM.RootShape
    (fun _ _ hl hr ↦ rootShape_append ((noCG_lbusTableCheckProg tabs _).1.reach_commits hl) hr)).mono
    (fun h ⟨hr, hD⟩ ↦ ⟨⟨rootShape_two hr, rootShape_firstWord hr, hD⟩, hr⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.M3
