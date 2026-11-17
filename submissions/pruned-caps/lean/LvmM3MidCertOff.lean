/- `LvmM3MidCertOff` (GOLF2 off-path move, group 10 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmLoopMleFast, LvmM3MidCert,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmLoopMleFast
import LvmM3MidCert
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert

-- ===== from `LvmLoopMleFast` =====

section
namespace Lvm.M3
open Lvm.Loop

theorem getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_of_ge {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem mkBC_rank (B : Block) (sK sE : Nat) (τ : Ty) (t : Nat) :
    (mkBC B sK sE).rank τ t = B.rank τ t := by
  unfold BC.rank
  split
  · rename_i h
    have key : ∀ τ', (psums (B.tpl.map (Row.w τ')) 0).toArray.getD t 0 = B.rank τ' t := by
      intro τ'
      rw [toArray_getD, psums_getD _ _ _ (by simp only [List.length_map]; exact h), Nat.zero_add,
        ← List.map_take]; rfl
    cases τ <;> exact key _
  · rfl

theorem mkBC_start (B : Block) (sK sE : Nat) : ∀ τ : Ty, (mkBC B sK sE).start τ = match τ with
    | .K => sK | .E => sE
  | .K => rfl
  | .E => rfl

theorem mkBC_tw (B : Block) (sK sE : Nat) : ∀ τ : Ty, (mkBC B sK sE).tw τ = B.tw τ
  | .K => rfl
  | .E => rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem start_eq_psums (Q : Program) (τ : Ty) (b : Nat) (hb : b ≤ Q.blocks.length) :
    (psums (Q.blocks.map fun B => B.tw τ * B.size) (Q.nIn τ)).getD b 0 = Q.start τ b := by
  rw [psums_getD _ _ _ (by simpa using hb), ← List.map_take]; rfl

theorem cache_bc (Q : Program) (b : Nat) :
    (cache Q).bc b = mkBC (Q.blk b) (Q.start .K b) (Q.start .E b) := by
  unfold PC.bc
  split
  · rename_i h
    simp only [cache, List.size_toArray, List.length_map, List.length_zip, length_psums] at h
    have hb : b < Q.blocks.length := by omega
    simp only [cache, List.getElem_toArray, List.getElem_map, List.getElem_zip]
    have hk := start_eq_psums Q .K b (Nat.le_of_lt hb)
    have he := start_eq_psums Q .E b (Nat.le_of_lt hb)
    simp only [Program.nIn] at hk he
    rw [getD_of_lt _ _ _ (by simp [length_psums]; omega)] at hk he
    rw [hk, he]
    simp [Program.blk, List.getElem?_eq_getElem hb]
  · rfl

theorem cache_pieceOf (Q : Program) (n : Nat) :
    (cache Q).pieceOf n = (Q.pieces.getD n default, (Q.pieces.getD n default).ts.toArray) := by
  unfold PC.pieceOf
  split
  · rename_i h
    simp only [cache, List.size_toArray, List.length_map] at h
    simp [cache, List.getElem?_eq_getElem h]
  · rename_i h
    simp only [cache, List.size_toArray, List.length_map, Nat.not_lt] at h
    rw [getD_of_ge _ _ _ h]; rfl

theorem cache_glue (Q : Program) : (cache Q).glue = Q.glueCols := rfl

theorem cache_Q (Q : Program) : (cache Q).Q = Q := rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem colAffineF_eq (Q : Program) (p : Piece) (c : FCol) (t : Nat) :
    colAffineF ((cache Q).bc p.blk) c t = Q.colAffine p c t := by
  rw [cache_bc]
  unfold colAffineF Program.colAffine
  have ht : (mkBC (Q.blk p.blk) (Q.start .K p.blk) (Q.start .E p.blk)).tpl.getD t default =
      (Q.blk p.blk).tpl.getD t default := toArray_getD _ _ _
  rw [ht]
  cases c with
  | res =>
    simp only [mkBC_rank, mkBC_tw]
    congr 1
    cases ((Q.blk p.blk).tpl.getD t default).ty <;> rfl
  | arg o => rfl
  | k => rfl
  | k' => rfl
  | F => rfl

theorem fvalBasic_k (Q : Program) (p : Piece) (c : FCol) (hc : c = .k ∨ c = .k') (i : Nat) :
    Q.fvalBasic p c ((Q.blk p.blk).size * i) =
      kOf c ((Q.blk p.blk).tpl.getD (p.ts.getD i 0) default).op := by
  have hs : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  have h1 : (Q.blk p.blk).size * i % (Q.blk p.blk).size = 0 := Nat.mul_mod_right _ _
  have h2 : (Q.blk p.blk).size * i / (Q.blk p.blk).size = i := Nat.mul_div_cancel_left _ hs
  rcases hc with rfl | rfl <;>
  · simp only [Program.fvalBasic, Program.pinst, Program.inst, h1, h2]
    rcases ((Q.blk p.blk).tpl.getD (p.ts.getD i 0) default).op with _ | _ | _ | _ | _ | _ | ⟨_ | _, _ | _⟩ <;> rfl

/-- **The cached closed form is WP-10's.** -/
theorem pieceEvalF_eq (Q : Program) (p : Piece) (c : FCol) (r : List FE) :
    pieceEvalF (cache Q) (p, p.ts.toArray) c r = Q.pieceEval p c r := by
  have hB : ((cache Q).bc p.blk).B = Q.blk p.blk := by rw [cache_bc]; rfl
  have hts : ∀ i, p.ts.toArray.getD i 0 = p.ts.getD i 0 := fun i => toArray_getD _ _ _
  unfold pieceEvalF Program.pieceEval
  simp only [hB]
  cases c with
  | res =>
    simp only [hts]
    refine congrArg (tplSum _) (funext fun i => ?_)
    rw [colAffineF_eq]
  | arg o =>
    simp only [hts]
    refine congrArg (tplSum _) (funext fun i => ?_)
    rw [colAffineF_eq]
  | k =>
    simp only [hts]
    refine congrArg (tplSum _) (funext fun i => ?_)
    rw [fvalBasic_k Q p .k (Or.inl rfl), cache_bc]
    simp only [mkBC, toArray_getD]
  | k' =>
    simp only [hts]
    refine congrArg (tplSum _) (funext fun i => ?_)
    rw [fvalBasic_k Q p .k' (Or.inr rfl), cache_bc]
    simp only [mkBC, toArray_getD]
  | F => rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem heightF_eq (Q : Program) (p : Piece) : heightF (cache Q) p = Q.height p := by
  rw [heightF, cache_bc]; rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem fixFEvalF_eq (Q : Program) (p : Piece) (r : List FE) :
    fixFEvalF (cache Q) p r = fixFEval Q p r := by
  have hB : ((cache Q).bc p.blk).B = Q.blk p.blk := by rw [cache_bc]; rfl
  unfold fixFEvalF fixFEval
  simp only [hB, cache_glue, heightF_eq, pieceEvalF_eq]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem pieceFixEvalF_eq (Q : Program) (p : Piece) (c : FCol) (r : List FE) :
    pieceFixEvalF (cache Q) (p, p.ts.toArray) c r = pieceFixEval Q p c r := by
  cases c <;> simp only [pieceFixEvalF, pieceFixEval, fixFEvalF_eq, pieceEvalF_eq]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem grpEvalF_eq (Q : Program) (g : Grp) : grpEvalF (cache Q) g = grpEval Q g := by
  funext c r
  unfold grpEvalF grpEval
  simp only [cache_pieceOf, heightF_eq, pieceFixEvalF_eq]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem mleF_eq : ∀ (r : List FE) (f : Nat → FE), mleF r f = mle r f
  | [], _ => rfl
  | r :: rs, f => by simp only [mleF, mle, mleF_eq rs]; ring

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem boxMul_eq (a : FE) (dims s : List Nat) (r : List FE) : boxMul a dims s r = a * boxEval dims s r := by
  cases dims with
  | nil => simp only [boxMul, boxEval, mul_one]
  | cons _ _ => rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem cacheG_C (Q : Program) : (cacheG Q).C = cache Q := rfl

theorem cacheG_glueE (Q : Program) :
    (cacheG Q).glueE = Q.glueCols.map fun x => (mkPE ((cache Q).bc x.1.blk) x.1, x.2) := rfl

theorem cacheG_pe (Q : Program) (n : Nat) :
    (cacheG Q).pe n = mkPE ((cache Q).bc (Q.pieces.getD n default).blk) (Q.pieces.getD n default) := by
  unfold PG.pe
  split
  · rename_i h
    simp only [cacheG, List.size_toArray, List.length_map] at h
    simp [cacheG, List.getElem?_eq_getElem h]
  · rename_i h
    simp only [cacheG, List.size_toArray, List.length_map, Nat.not_lt] at h
    rw [getD_of_ge _ _ _ h]; rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem pieceEvalG_eq (Q : Program) (p : Piece) (c : FCol) (r : List FE) :
    pieceEvalG (cacheG Q) (mkPE ((cache Q).bc p.blk) p) c r = Q.pieceEval p c r := by
  rw [← pieceEvalF_eq]
  unfold pieceEvalG pieceEvalF
  cases c with
  | res =>
    simp only [cacheG_C, mkPE_p, mkPE_ts, mleF_eq, tplSum]
    congr 1; funext i
    rw [boxMul_eq, coefF_eq]
    simp only [coefS]
  | arg o =>
    simp only [cacheG_C, mkPE_p, mkPE_ts, mleF_eq, tplSum]
    congr 1; funext i
    rw [boxMul_eq, coefF_eq]
    simp only [coefS]
  | k =>
    simp only [cacheG_C, mkPE_p, mkPE_ts, mleF_eq, tplSum]
    congr 1; funext i
    rw [coefF_eq]; rfl
  | k' =>
    simp only [cacheG_C, mkPE_p, mkPE_ts, mleF_eq, tplSum]
    congr 1; funext i
    rw [coefF_eq]; rfl
  | F => rfl

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem zipIdx_map' {α β : Type} (f : α → β) : ∀ (l : List α) (k : Nat),
    (l.map f).zipIdx k = (l.zipIdx k).map fun x => (f x.1, x.2)
  | [], _ => rfl
  | a :: l, k => by simp only [List.map_cons, List.zipIdx_cons, zipIdx_map' f l (k + 1)]

theorem fixFEvalG_eq (Q : Program) (p : Piece) (r : List FE) :
    fixFEvalG (cacheG Q) p r = fixFEval Q p r := by
  rw [← fixFEvalF_eq]
  unfold fixFEvalG fixFEvalF
  simp only [cacheG_glueE, cacheG_C, zipIdx_map', List.map_map, cache_glue]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, heightF, mkPE_p, pieceEvalG_eq, pieceEvalF_eq]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

theorem grpEvalG_eq (Q : Program) (g : Grp) : grpEvalG (cacheG Q) g = grpEval Q g := by
  funext c r
  unfold grpEvalG grpEval
  -- `congrArg`, not `congr 1`: its closing `rfl` attempt unfolds the `FE` products (17 s)
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  intro x _
  have hp : ((cacheG Q).pe x.1).p = Q.pieces.getD x.1 default := by rw [cacheG_pe]; rfl
  have hC : (cacheG Q).C = cache Q := rfl
  simp only [hp, hC, heightF_eq]
  congr 1
  cases c <;> simp only [pieceFixEvalG, pieceFixEval, cacheG_pe, pieceEvalG_eq, mkPE_p, fixFEvalG_eq]

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

/-- **They are WP-9's tables.** -/
theorem lvmTabsC_eq (Q : Program) (pl : Nat → Var → Bool × Nat) (groups : List Grp)
    (arrs : List InArr) (aux : List Tab) :
    lvmTabsC (cacheG Q) pl groups arrs aux = lvmTabs Q pl groups arrs aux := by
  unfold lvmTabsC lvmTabs grpTab
  simp only [grpEvalG_eq]
  rfl

/-- `lvmTabsC` with the cache built in place. -/
def lvmTabsF (Q : Program) (pl : Nat → Var → Bool × Nat) (groups : List Grp) (arrs : List InArr)
    (aux : List Tab) : List Tab :=
  lvmTabsC (cacheG Q) pl groups arrs aux

theorem lvmTabsF_eq (Q : Program) (pl : Nat → Var → Bool × Nat) (groups : List Grp)
    (arrs : List InArr) (aux : List Tab) :
    lvmTabsF Q pl groups arrs aux = lvmTabs Q pl groups arrs aux := lvmTabsC_eq Q pl groups arrs aux

end Lvm.M3
end

section
namespace Lvm.M3
open Lvm.Loop

/-- The evaluator is the extension (every point). -/
theorem pubEval_eq (vals : List FK) (r : List FE) :
    pubEval vals r = mle r fun x => FE.ofK (pubCell vals x) := by
  simp only [pubEval, toArray_getD, pubCell]
  exact mleF_eq _ _

end Lvm.M3
end

-- ===== from `LvmM3MidCert` =====

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
variable (L : Lay)
variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

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
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck LeanVM.Protocol.Whir.Sound CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

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

end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck LeanVM.Protocol.Whir.Sound CompPoly CMlPolynomialEval
open scoped NNReal ENNReal
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
end
