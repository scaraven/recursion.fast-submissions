-- New for lvm6 (WP CC8). The glue step of the final weight cell `wFinG` (NODE §6a (ii), CC-8g of
-- `Lvm6QCFinStmt`): from a weight gadget of a level, the next level's weight gadget adds the OOD
-- term `λ·eq(z, y)` and the query terms `λ^(k+2)·∏_i ((1 − y_i) + y_i·Ŵ_i(K(p_k)))` at the point
-- `y` = the next level's fold challenges, then the tail point. The fold of an admitted (multiaffine)
-- table is evaluation (`foldsT_MA`), so the previous level's gadget is called at the longer point.
import Lvm6QCFin

/-!
# The glue step of `wFinG` (generator and proof)

* `foldsT`, `wFolds_snd`, **`foldsT_MA`**: the folded table is the table at `α ++ y` when it is
  affine in each folded variable.
* `prodFG`, `hsA_prodFG`: a product `∏_{i<n} a_i(y_i)` (W1's `prodL`) with one factor gadget call per
  factor; `eqFac` (`1 + z_i + y_i`) and `colFac` (`1 + y_i·w_i + y_i`) in characteristic 2,
  `eqL_eq`, `colL_eq`.
* `colsG`, `hsA_colsG`: one instance per query position (the `Ŵ` gadget, the factor product, the
  power of `λ` carried as a cell).
* `glueG`; **`glueHar : WGlueStmt glueG`**.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK

variable {c : Ctx} {M : Mem}

/-! ## Folds of tables -/

/-- A table folded by a list of challenges, first first (W1's `foldTab`). -/
noncomputable def foldsT : List E2 → (List E2 → E2) → (List E2 → E2)
  | [], Φ => Φ
  | α :: as, Φ => foldsT as (Whir.foldTab Φ α)

theorem wFolds_snd : ∀ (j : ℕ) (rs : List (Whir.Rnd E2)) (w : Whir.WtE.Wt (0 + j)),
    rs.length = j → (Whir.wFolds (m := 0) Whir.WtE j rs w).2 = foldsT (rs.map (·.α)) w.2
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, h => absurd h (by simp)
  | _ + 1, [], _, h => absurd h (by simp)
  | j + 1, r :: rs, w, h => wFolds_snd j rs (Whir.WtE.wFold w r.α) (by simpa using h)

/-- **Folding an affine table is evaluating it.** -/
theorem foldsT_MA : ∀ (as : List E2) (Φ : List E2 → E2) (n : ℕ), Whir.MA (as.length + n) Φ →
    ∀ y, foldsT as Φ y = Φ (as ++ y)
  | [], _, _, _, _ => rfl
  | α :: as, Φ, n, h, y => by
    have h' : Whir.MA (as.length + n + 1) Φ := by
      rwa [show as.length + n + 1 = (α :: as).length + n by simp only [List.length_cons]; omega]
    show foldsT as (Whir.foldTab Φ α) y = Φ (α :: (as ++ y))
    rw [foldsT_MA as _ n (Whir.MA.fold h' α) y]
    exact (h'.1 α (as ++ y)).symm

theorem rndsRep_alpha {rc : List RndC} {rs : List (Whir.Rnd E2)} (h : RndsRep M rc rs) :
    (rc.map (·.α)).map (ev2 M) = rs.map (·.α) := by
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    simp only [List.map_cons, ih]
    rw [h1.2.2.2.2.1]

/-! ## Products of affine factors -/

/-- `∏_{i<n} a_i(y_i)` (`y_i` the cells of `y`, the zero `z` past its end), one `fac` call each. -/
def prodFG (z one : C2) : (ℕ → C2 → BM C2) → ℕ → List C2 → BM C2
  | _, 0, _ => pure one
  | fac, n + 1, y => fac 0 (y.headD z) >>= fun f ↦ prodFG z one (fun j ↦ fac (j + 1)) n y.tail >>=
      fun p ↦ g2Mul f p z

theorem hsA_prodFG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) :
    ∀ (n : ℕ) (fac : ℕ → C2 → BM C2) (a : ℕ → E2 → E2),
      (∀ i x, HsA c M (fac i x) fun r ↦ ev2 M r = a i (ev2 M x)) → ∀ y : List C2,
      HsA c M (prodFG z one fac n y) fun r ↦ ev2 M r = Whir.prodL a n (y.map (ev2 M))
  | 0, _, _, _, _ => hsA_pure hone
  | n + 1, fac, a, hfac, y =>
    hsA_bind (hfac 0 (y.headD z)) fun f hf ↦
      hsA_bind (hsA_prodFG hz hone n (fun j ↦ fac (j + 1)) (fun j ↦ a (j + 1))
        (fun i x ↦ hfac (i + 1) x) y.tail) fun p hp ↦
      hsA_mono (hsA_of_hs (hs_g2Mul f p z)) fun r hr ↦ by
        have e1 : (y.map (ev2 M)).headD 0 = ev2 M (y.headD z) := by
          cases y <;> simp [ev2_of_zero hz]
        have e2 : (y.map (ev2 M)).tail = y.tail.map (ev2 M) := by cases y <;> rfl
        rw [ev2_mul hr, ev2_of_zero hz, add_zero, hf, hp]
        show _ = a 0 ((y.map (ev2 M)).headD 0) * Whir.prodL (fun j ↦ a (j + 1)) n (y.map (ev2 M)).tail
        rw [e1, e2]

theorem prodL_congr : ∀ (n : ℕ) (a b : ℕ → E2 → E2) (y : List E2),
    (∀ i < n, ∀ X, a i X = b i X) → Whir.prodL a n y = Whir.prodL b n y
  | 0, _, _, _, _ => rfl
  | n + 1, a, b, y, h => by
    show a 0 _ * _ = b 0 _ * _
    rw [h 0 (by omega), prodL_congr n _ _ _ fun i hi X ↦ h (i + 1) (by omega) X]

/-- The OOD factor `1 + z_i + y_i` (characteristic 2: `z·y + (1 − z)(1 − y)`). -/
def eqFac (z one : C2) (zs : List C2) (i : ℕ) (x : C2) : BM C2 :=
  g2Add (zs.getD i z) x >>= fun s ↦ g2Add one s

theorem hs_eqFac {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (zs : List C2) (i : ℕ)
    (x : C2) : Hs c M (eqFac z one zs i x) fun r ↦
      ev2 M r = 1 + ((zs.map (ev2 M)).getD i 0 + ev2 M x) :=
  hs_bind (hs_g2Add _ _) fun s hs ↦ hs_mono (hs_g2Add _ _) fun r hr ↦ by
    rw [ev2_add hr, ev2_add hs, hone, ev2_getD (ev2_of_zero hz)]

/-- The query factor `1 + y_i·w_i + y_i` (characteristic 2: `(1 − y) + y·w`). -/
def colFac (z one : C2) (ws : List C2) (i : ℕ) (x : C2) : BM C2 :=
  g2Mul x (ws.getD i z) x >>= fun t ↦ g2Add one t

theorem hs_colFac {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (ws : List C2) (i : ℕ)
    (x : C2) : Hs c M (colFac z one ws i x) fun r ↦
      ev2 M r = 1 + (ev2 M x * (ws.map (ev2 M)).getD i 0 + ev2 M x) :=
  hs_bind (hs_g2Mul _ _ _) fun s hs ↦ hs_mono (hs_g2Add _ _) fun r hr ↦ by
    rw [ev2_add hr, ev2_mul hs, hone, ev2_getD (ev2_of_zero hz)]

theorem eqL_eq {ν : ℕ} (zv : Fin ν → E2) (zl : List E2) (hz : zl = List.ofFn zv) (y : List E2) :
    Whir.eqL zv y = Whir.prodL (fun i X ↦ 1 + (zl.getD i 0 + X)) ν y := by
  refine prodL_congr ν _ _ y fun i hi X ↦ ?_
  rw [dif_pos hi, hz, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  linear_combination (zv ⟨i, hi⟩ * X - X - zv ⟨i, hi⟩) * two_E2

theorem colL_eq (κ x : ℕ) (wl : List E2)
    (hw : wl = (List.range κ).map fun i ↦ algebraMap K E2 (normVanishingAt i (K.ofBits x)))
    (y : List E2) :
    Whir.colL κ x y = Whir.prodL (fun i X ↦ 1 + (X * wl.getD i 0 + X)) κ y := by
  refine prodL_congr κ _ _ y fun i hi X ↦ ?_
  rw [hw, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  linear_combination (-X) * two_E2

/-! ## The query terms -/

/-- `Σ_k λ^(m+k+2)·col(x_k)`. -/
noncomputable def colsV (lam : E2) (col : ℕ → E2) : List ℕ → ℕ → E2
  | [], _ => 0
  | x :: xs, m => lam ^ (m + 2) * col x + colsV lam col xs (m + 1)

theorem colsV_ofFn (lam : E2) (col : ℕ → E2) : ∀ (t : ℕ) (f : Fin t → ℕ) (m : ℕ),
    colsV lam col (List.ofFn f) m = ∑ k : Fin t, lam ^ (m + (k : ℕ) + 2) * col (f k)
  | 0, _, _ => by simp [colsV]
  | t + 1, f, m => by
    rw [List.ofFn_succ, colsV, colsV_ofFn lam col t, Fin.sum_univ_succ]
    have e : ∀ k : Fin t, m + 1 + (k : ℕ) + 2 = m + ((k.succ : Fin (t + 1)) : ℕ) + 2 :=
      fun k ↦ by simp only [Fin.val_succ]; omega
    simp only [e, Fin.val_zero, Nat.add_zero]

/-- **The query terms**, one instance per position cell: `pw` the cell of `λ^(m+1)`, `λ^(m+2)`
next, the position's `Ŵ` cells from `whG`, the factor product at `y`, accumulated. -/
def colsG (z one : C2) (whG : Cell → Cell → BM (List C2)) (lam : C2) (y : List C2) (ν : ℕ)
    (gate : Cell) : List Cell → C2 → C2 → BM C2
  | [], _, acc => pure acc
  | x :: xs, pw, acc => g2Mul pw lam z >>= fun pw' ↦ whG x gate >>= fun ws ↦
      prodFG z one (colFac z one ws) ν y >>= fun cv ↦ g2Mul pw' cv acc >>= fun acc' ↦
        colsG z one whG lam y ν gate xs pw' acc'

theorem hsA_colsG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1)
    {whG : Cell → Cell → BM (List C2)} {ν : ℕ} (hwh : WhAt ν whG) {gate : Cell}
    (hg : gate.val M = 1) (lam : C2) (y : List C2) : ∀ (xs : List Cell) (m : ℕ) (pw acc : C2),
      ev2 M pw = ev2 M lam ^ (m + 1) →
      HsA c M (colsG z one whG lam y ν gate xs pw acc) fun r ↦ ev2 M r = ev2 M acc +
        colsV (ev2 M lam) (fun x ↦ Whir.colL ν x (y.map (ev2 M))) (xs.map fun x ↦ kToNat (kv M x)) m
  | [], _, _, _, _ => hsA_pure (by simp [colsV])
  | x :: xs, m, pw, acc, hpw =>
    hsA_bind (hsA_of_hs (hs_g2Mul pw lam z)) fun pw' hpw' ↦
      hsA_bind (hwh c M x gate hg) fun ws hws ↦
      hsA_bind (hsA_prodFG hz hone ν (colFac z one ws)
        (fun i X ↦ 1 + (X * (ws.map (ev2 M)).getD i 0 + X))
        (fun i x' ↦ hsA_of_hs (hs_colFac hz hone ws i x')) y) fun cv hcv ↦
      hsA_bind (hsA_of_hs (hs_g2Mul pw' cv acc)) fun acc' hacc' ↦
      hsA_mono (hsA_colsG hz hone hwh hg lam y xs (m + 1) pw' acc' (by
        rw [ev2_mul hpw', ev2_of_zero hz, add_zero, hpw]
        ring)) fun r hr ↦ by
        have hp1 : ev2 M pw' = ev2 M lam ^ (m + 2) := by
          rw [ev2_mul hpw', ev2_of_zero hz, add_zero, hpw]
          ring
        rw [hr, ev2_mul hacc', hp1, hcv, ← colL_eq ν _ _ hws]
        simp only [List.map_cons, colsV]
        ring

/-! ## The glue step -/

/-- **The glue step of `wFinG`**: at the point `y` = the next level's `α` cells then `τ`, the
previous level's weight cell (`wGp` at `y`), plus `λ·eq(z, y)`, plus the query terms. -/
def glueG (wGp : List RndC → List C2 → Cell → BM C2) (whG : Cell → Cell → BM (List C2))
    (rcP : List RndC) (oc : TailOutC) (rc : List RndC) (τ : List C2) (gate : Cell) : BM C2 :=
  let y := rc.map (·.α) ++ τ
  wGp rcP y gate >>= fun pv ↦
  g2Zero oc.lam >>= fun z ↦ g2Const 1 z >>= fun one ↦
  prodFG z one (eqFac z one oc.z) oc.z.length y >>= fun ev ↦
  g2Mul oc.lam ev pv >>= fun acc ↦
  colsG z one whG oc.lam y oc.z.length gate oc.ps oc.lam acc

/-- **CC-8g proved**: the glue step builds the next level's weight gadget. -/
theorem glueHar : WGlueStmt glueG := by
  intro κ' ℓ' ko t h ℓ hκ w Pre wGp whG hwok hwp hwh rcP rs oc o hlenP c M hpre rc rs' hr' hl' τ
    hτ gate hgate
  obtain ⟨hP, hrP, hoc⟩ := hpre
  obtain ⟨_, hzs, _, hps, hlam, _⟩ := hoc
  have hν : oc.z.length = ko + 1 := by simpa using congrArg List.length hzs
  have hY : (rc.map (·.α) ++ τ).map (ev2 M) = rs'.map (·.α) ++ τ.map (ev2 M) := by
    rw [List.map_append, rndsRep_alpha hr']
  unfold glueG
  have hyl : (rc.map (·.α) ++ τ).length = w.1 := by
    have hτ' : τ.length = κ' := hτ
    rw [List.length_append, List.length_map, List.Forall₂.length_eq hr', hl', hτ', hwok.1]
    omega
  refine hsA_bind (hwp c M hP rcP rs hrP hlenP _ hyl gate hgate) fun pv hpv ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Zero oc.lam)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 z)) fun one hone ↦ ?_
  have hone' : ev2 M one = 1 := by
    show FE2.ringEquivE2 (one.val M) = 1
    rw [hone, map_one]
  refine hsA_bind (hsA_prodFG hz hone' oc.z.length (eqFac z one oc.z)
    (fun i X ↦ 1 + ((oc.z.map (ev2 M)).getD i 0 + X)) (fun i x ↦ hsA_of_hs (hs_eqFac hz hone' oc.z i x)) _) fun ev hev ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul oc.lam ev pv)) fun acc hacc ↦ ?_
  have hwh' : WhAt oc.z.length whG := by rw [hν]; exact hwh
  refine hsA_mono (hsA_colsG hz hone' hwh' hgate oc.lam _ oc.ps 0 oc.lam acc (by simp))
    fun r hr ↦ ?_
  -- the table side
  have hma : Whir.MA ((rs'.map (·.α)).length + κ')
      (Whir.wGlueE κ' ℓ' ko t h (Whir.wFolds Whir.WtE ℓ rs w) o).2 := by
    rw [List.length_map, hl']
    exact (Whir.hglue_E hκ w hwok rs o).2
  rw [wFolds_snd ℓ' rs' _ hl', foldsT_MA _ _ κ' hma, hr, ev2_mul hacc, hev, hpv, ← hY]
  have hps' : oc.ps.map (fun x ↦ kToNat (kv M x)) = List.ofFn fun k ↦ (o.ps k : ℕ) := hps
  rw [hps', colsV_ofFn, hν, ← eqL_eq o.z _ hzs, hlam]
  show _ = _ + o.lam * _ + _
  simp only [Nat.zero_add]
  ring

end Lvm6.QC
