-- New for lvm2 E2-FT (E2F-C5): `C_main`'s opening at S2GF in both shapes, the preparation (`prepZ`): what each
-- prepared claim weighs in the big and the small shape (`pfWB`, `pfWS`) and that the preparation of a circuit claim
-- standing for V's claim gives V's stack claim in the shape `b` that the shape cell holds (`SRel`, `prepZ_spec`).
import LvmE2QOpenPhaseT

/-!
# The preparation in both shapes

* **`FSmall`**, **`FRelZ`**: what a circuit claim stands for in V's list (`FRelT`) and its small shape's side (the
  regular blocks, V's tail).
* `rowLV`: the row leaf's value (`rowLeafGL_val`), `ν`-paired components; `rowLV_none`: V's `rowW`.
* **`pfWB`/`pfWS`**: a prepared claim's weight with the big / the moved top keys; `PFOk` its static form.
* **`SRel M s r sc`**: the prepared claim `r` gives V's stack claim `sc` (value; weight at `x` when `σ = 0`, at
  `rotZ x` with moved keys when `σ = 1`). **`prepZs_spec`**, **`pinZG_spec`**.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape Lvm.E2V Finset

/-! ## The relation of a circuit claim to V's, both shapes -/

/-- **The small shape's side of a circuit claim** whose V claim has tail `t` (`C_main` at `ν = 23`; the shape `b`:
an `E3` claim's tail is `tailC` in the small shape only, V's `D` boundary claims carry tail `0` in both). -/
def FSmall (M : Mem) (zc : Cell) (b : Bool) : FClaim → FE → Prop
  | .e3 cc, t => ZWF zc cc = true ∧ (b = true → t = tailC M cc)
  | .half _ parts _, t => (∀ e ∈ parts, RegP e.2.1) ∧ t = 0
  | .dhalf h zl _, t => ∃ (r : List FE2) (l : ℕ), l < 4 ∧ r.length = 20 ∧ zl.map (C2.val M) = r ++ selPtF l 2 ∧
      t = (tailDE2 r l).getD (if h then 1 else 0) 0
  | .row blk _ _ _, t => RegP blk ∧ t = 0
  | .drow zl nu _, t => (zl.map (C2.val M)).getD 22 0 = 0 ∧
      ∃ eqR, RowNuOk M nu eqR ∧ t = rowTailE2 eqR (zl.map (C2.val M))

/-- **What a circuit claim stands for in V's list, both shapes**: `FRelT` on `C_main` at `ν = 23` and `FSmall`. -/
def FRelZ (M : Mem) (zc : Cell) (b : Bool) (fc : FClaim) (cl : Com × BlockClaim × FE) : Prop :=
  FRelT M CMain.nu20 fc cl ∧ FSmall M zc b fc cl.2.2

/-- V's stack claim of a claim in shape `b` (`dOpenF`'s at `ν = 23`). -/
def scOf (b : Bool) (cl : Com × BlockClaim × FE) : StackClaim :=
  if b then onStackZB cl.2.1 cl.2.2 else cl.2.1.onStack

/-! ## The row leaf -/

/-- The `ν`-pairing of component `k` (the `ν` cells as the looped leaf reads them: iteration `(k + 63) mod 64`). -/
def Lnu (M : Mem) (nu : RowNu) (k : ℕ) (q : Rk k) : FE :=
  (nuAt nu.nu0 ((k + 63) % 64)).val M * q.re + (nuAt nu.nu1 ((k + 63) % 64)).val M * q.im

/-- The extra factor of a row leaf in component `k` (`κ ⊗ 1`). -/
def kapK (M : Mem) (k : ℕ) : Option C2 → Rk k
  | some cκ => zk k (cκ.val M)
  | none => 1

/-- **The row leaf's value** at `y`: `Σ_k L_k(pR(σ^k z, y)·σ^k κ)`. -/
def rowLV (M : Mem) (nu : RowNu) (zs : List C2) (κ : Option C2) (y : List FE) : FE :=
  ∑ k ∈ range 64, Lnu M nu k (pR ((zs.map (C2.val M)).map (zk k)) y * kapK M k κ)

theorem qk_foldl (k : ℕ) : ∀ (L : List (FE × FE)) (P : FE × FE),
    qk k (L.foldl (qm (twK k)) P) = qk k P * (L.map (qk k)).prod
  | [], P => by simp
  | a :: L, P => by rw [List.foldl_cons, qk_foldl k L, qk_qm, List.map_cons, List.prod_cons]; ring

variable {c : Ctx} {M : Mem}

theorem kcell_pow {x : Cell} (hx : x.ty = .K) (k : ℕ) : x.val M ^ 2 ^ k = FE.ofK ((x.val M).c₀ ^ 2 ^ k) := by
  conv_lhs => rw [← kcell_val hx]
  exact (map_pow FE.ofKRingHom _ _).symm

theorem fct_cell (x : C2) (hx : KC2 x) (e : FE) (k : ℕ) :
    ((1 + x.re.val M ^ 2 ^ k + e, x.im.val M ^ 2 ^ k) : FE × FE) = fct k (x.val M, e) := by
  show _ = (1 + FE.ofK ((x.re.val M).c₀ ^ 2 ^ k) + e, FE.ofK ((x.im.val M).c₀ ^ 2 ^ k))
  rw [← kcell_pow hx.1, ← kcell_pow hx.2]

theorem zk_cell (x : C2) (hx : KC2 x) (k : ℕ) : qk k (x.re.val M ^ 2 ^ k, x.im.val M ^ 2 ^ k) = zk k (x.val M) := by
  show _ = qk k (FE.ofK ((x.re.val M).c₀ ^ 2 ^ k), FE.ofK ((x.im.val M).c₀ ^ 2 ^ k))
  rw [← kcell_pow hx.1, ← kcell_pow hx.2]

/-- **The looped row leaf's cells hold `rowLV`** at the point's copies `xb + l` (`hs_rowLeafGL`). -/
theorem rowLeafGL_val (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : ℕ) {z zk' : Cell} (hz : z.val M = 0)
    (hzk : zk'.val M = 0) (hne : zs ≠ []) (hK : ∀ x ∈ zs, KC2 x) (hκ : ∀ cκ, κ = some cκ → KC2 cκ) :
    Hs c M (rowLeafGL nu zs κ xb z zk') (fun r =>
      r.val M = rowLV M nu zs κ ((List.range zs.length).map fun l => M.e (xb + l))) := by
  refine hs_mono (hs_rowLeafGL nu zs κ xb hz hzk hne hK hκ) fun r hv => ?_
  rw [hv, rowLV]
  refine sum_congr rfl fun k _ => ?_
  have e : qk k (crtL M zs κ xb k) =
      pR ((zs.map (C2.val M)).map (zk k)) ((List.range zs.length).map fun l => M.e (xb + l)) * kapK M k κ := by
    rw [crtL, qk_foldl]
    unfold crtF
    rw [show qk k (1, 0) = 1 from rfl, one_mul, List.map_append, List.prod_append]
    congr 1
    · rw [pR]
      congr 1
      apply List.ext_getElem (by simp)
      intro l h1 h2
      simp only [List.length_map, List.length_range] at h1
      obtain ⟨hre, him⟩ := hK _ (List.getElem_mem h1)
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
      rw [List.getD_eq_getElem _ _ h1, fct_cell _ ⟨hre, him⟩, qk_fct]
    · cases κ with
      | none => rfl
      | some cκ =>
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, kapK]
        exact zk_cell cκ (hκ cκ rfl) k
  show _ = Lnu M nu k _
  rw [← e]
  rfl

theorem Lnu_eq (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) {k : ℕ} (hk : k < 64) (q : Rk k) :
    Lnu M nu k q = Lk (fun j => eqR.getD j 0) k q := by
  rw [Lnu, (hnu.2 k hk).1, (hnu.2 k hk).2]
  rfl

/-- **Without `κ` the row leaf is V's row weight.** -/
theorem rowLV_none (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) (zs : List C2) (y : List FE) :
    rowLV M nu zs none y = rowW eqR (zs.map (C2.val M)) y := by
  rw [rowLV, rowW_comp]
  refine sum_congr rfl fun k hk => ?_
  rw [Lnu_eq nu eqR hnu (mem_range.mp hk), kapK, mul_one]

/-- **With `κ = 1` the row leaf is V's row weight.** -/
theorem rowLV_one (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) (zs : List C2) (y : List FE) (κ : C2)
    (hκ : κ.val M = 1) : rowLV M nu zs (some κ) y = rowW eqR (zs.map (C2.val M)) y := by
  rw [← rowLV_none nu eqR hnu]
  refine sum_congr rfl fun k _ => ?_
  rw [kapK, kapK, hκ, zk_one]

/-! ## The prepared claims' weights -/

/-- **A prepared claim's weight with the big keys** at `y`. -/
def pfWB (M : Mem) : PF → List FE → FE
  | .e3 cc _ => (cc.val M).2.onStack.1
  | .half h parts _ => fun y => ((partsV M parts).map fun e => (partH h e).onStack.1 y).sum
  | .row blk z κ nu _ => fun y => blk.eqAbove y * rowLV M nu z κ (y.take blk.variableCount)

/-- **A prepared claim's weight with the moved keys** (regular claims; the others as `pfWB`). -/
def pfWS (M : Mem) : PF → List FE → FE
  | .e3 cc reg => if reg then smallW M cc else (cc.val M).2.onStack.1
  | .half h parts reg => fun y => if reg then ((partsV M parts).map fun e => (shiftB (partH h e)).onStack.1 y).sum
      else ((partsV M parts).map fun e => (partH h e).onStack.1 y).sum
  | .row blk z κ nu reg => fun y => (if reg then shiftP blk else blk).eqAbove y * rowLV M nu z κ (y.take blk.variableCount)

/-- **The static form of a prepared claim** (`ν = 23`). -/
def PFOk : PF → Prop
  | .e3 cc reg => WF1 CMain.nu20 cc = true ∧ (reg = true → RegC cc)
  | .half _ parts reg => ∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
      (if reg then RegP e.2.1 else e.2.1.variableCount ≤ CMain.nu20)
  | .row blk z κ _ reg => z ≠ [] ∧ (∀ x ∈ z, KC2 x) ∧ (∀ cκ, κ = some cκ → KC2 cκ) ∧
      z.length = blk.variableCount ∧ blk.variableCount ≤ CMain.nu20 ∧ (reg = true → RegP blk)

/-- **A prepared claim gives V's stack claim** `sc` (shape cell `s`). -/
structure SRel (M : Mem) (s : Cell) (r : PF × Cell) (sc : StackClaim) : Prop where
  ok : PFOk r.1
  value : r.2.val M = sc.2
  big : s.val M = 0 → ∀ x : List FE, x.length = CMain.nu20 → pfWB M r.1 x = sc.1 x
  small : s.val M = 1 → ∀ x : List FE, x.length = CMain.nu20 → pfWS M r.1 (rotZ x) = sc.1 x

theorem srel_mk {s : Cell} {b : Bool} (hs : s.val M = if b then 1 else 0) {r : PF × Cell} {sc : StackClaim}
    (ok : PFOk r.1) (value : r.2.val M = sc.2)
    (hB : b = false → ∀ x : List FE, x.length = CMain.nu20 → pfWB M r.1 x = sc.1 x)
    (hS : b = true → ∀ x : List FE, x.length = CMain.nu20 → pfWS M r.1 (rotZ x) = sc.1 x) : SRel M s r sc := by
  refine ⟨ok, value, fun h0 => hB ?_, fun h1 => hS ?_⟩
  · cases b
    · rfl
    · rw [hs] at h0; exact absurd h0 one_ne_zero
  · cases b
    · rw [hs] at h1; exact absurd h1.symm one_ne_zero
    · rfl

/-! ## The muxing gadgets -/

theorem sK2_val {F : FCtx} (hF : FCtxOk M F) {sK : Cell} {b : Bool} (hsK : sK.val M = if b then 1 else 0) :
    (kC2 sK F.zk).val M = if b then 1 else 0 := by
  show (⟨(sK.val M).c₀, (F.zk.val M).c₀⟩ : FE2) = _
  rw [hsK, hF.zk]
  cases b <;> rfl

theorem mux2_spec {F : FCtx} {sK : Cell} {b : Bool} (hs2 : (kC2 sK F.zk).val M = if b then 1 else 0) (a a' : C2) :
    Hs c M (mux2 F sK a a') (fun r => KC2 r ∧ r.val M = if b then a'.val M else a.val M) := by
  unfold mux2
  refine hs_bind (hs_g2Add a a') fun d hd => hs_and (g2Mul_K _ _ _) (hs_mono (hs_g2Mul _ _ _) fun r hr => ?_)
  rw [hr, hd, hs2]
  cases b
  · simp
  · simp only [if_true, one_mul]
    rw [add_comm (a.val M) (a'.val M), add_assoc, fe2_add_self, add_zero]

theorem kappa2_spec {F : FCtx} (hF : FCtxOk M F) (z : List C2) (hz : 20 ≤ z.length) :
    Hs c M (kappa2 F z) (fun κ => KC2 κ ∧ κ.val M = kapE (z.map (C2.val M))) := by
  unfold kappa2
  exact hs_bind (hs_g2One _) fun a ha => hs_bind (hs_g2One _) fun b hb =>
    hs_and (g2Mul_K _ _ _) (hs_mono (hs_g2Mul _ _ _) fun r hr => by
      rw [hr, ha, hb, hF.z2, add_zero, kapE, c2_getD z (by omega), c2_getD z (by omega)])

theorem split18 (l : List FE2) (h : 22 ≤ l.length) :
    l.take 18 ++ [l.getD 18 0, l.getD 19 0, l.getD 20 0, l.getD 21 0] ++ l.drop 22 = l := by
  conv_rhs => rw [← List.take_append_drop 22 l]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_append, List.length_take, List.length_cons, List.length_nil] at h1
  by_cases hi : i < 18
  · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem_take]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_take]
    have : i - min 18 l.length < 4 := by omega
    have hm : min 18 l.length = 18 := by omega
    simp only [List.length_take, hm]
    have : i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 := by omega
    have e18 : l.getD 18 0 = l[18] := List.getD_eq_getElem _ _ (by omega)
    have e19 : l.getD 19 0 = l[19] := List.getD_eq_getElem _ _ (by omega)
    have e20 : l.getD 20 0 = l[20] := List.getD_eq_getElem _ _ (by omega)
    have e21 : l.getD 21 0 = l[21] := List.getD_eq_getElem _ _ (by omega)
    rcases this with rfl | rfl | rfl | rfl <;> simp only [e18, e19, e20, e21] <;> rfl

/-- **The muxed `D` point and scale** (`muxD`): `(1, z)` in the big shape, `(κ, z₀…₁₇ ‖ z₂₀ z₂₁ 0 0 ‖ z₂₂…)` small. -/
theorem muxD_spec {F : FCtx} (hF : FCtxOk M F) {sK : Cell} {b : Bool}
    (hs2 : (kC2 sK F.zk).val M = if b then 1 else 0) (z : List C2) (hz : 22 ≤ z.length) (hzK : ∀ x ∈ z, KC2 x)
    (κ : C2) :
    Hs c M (muxD F sK z κ) (fun r => KC2 r.1 ∧ (∀ x ∈ r.2, KC2 x) ∧ r.2.length = z.length ∧
      r.1.val M = (if b then κ.val M else 1) ∧
      r.2.map (C2.val M) = if b then (z.map (C2.val M)).take 18 ++
        [(z.map (C2.val M)).getD 20 0, (z.map (C2.val M)).getD 21 0, 0, 0] ++ (z.map (C2.val M)).drop 22
      else z.map (C2.val M)) := by
  unfold muxD
  refine hs_bind (mux2_spec hs2 _ _) fun κm ⟨hk1, hk2⟩ => hs_bind (mux2_spec hs2 _ _) fun m18 ⟨h18, v18⟩ =>
    hs_bind (mux2_spec hs2 _ _) fun m19 ⟨h19, v19⟩ => hs_bind (mux2_spec hs2 _ _) fun m20 ⟨h20, v20⟩ =>
    hs_bind (mux2_spec hs2 _ _) fun m21 ⟨h21, v21⟩ => hs_pure ⟨hk1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with (hx | rfl | rfl | rfl | rfl) | hx
    · exact hzK x (List.mem_of_mem_take hx)
    · exact h18
    · exact h19
    · exact h20
    · exact h21
    · exact hzK x (List.mem_of_mem_drop hx)
  · simp; omega
  · rw [hk2, hF.o2]
  · rw [List.map_append, List.map_append, List.map_take, List.map_drop]
    simp only [List.map_cons, List.map_nil]
    rw [v18, v19, v20, v21, hF.z2]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [c2_getD z (by omega), c2_getD z (by omega), c2_getD z (by omega), c2_getD z (by omega),
        split18 _ (by simpa using hz)]
    · simp only [if_true]
      rw [c2_getD z (by omega), c2_getD z (by omega)]

/-- `zF(a, b)` over `E2` (`zF2`'s value). -/
def zFE2 (x y : FE2) : FE2 :=
  FE2.ofK (zK 0 + zK 1) * x + FE2.ofK (zK 0) + FE2.ofK (zK 0 + zK 2) * y + FE2.ofK (zK 0 + zK 1 + zK 2 + zK 3) * (x * y)

theorem zF2_spec {F : FCtx} (hF : FCtxOk M F) (a b : C2) :
    Hs c M (zF2 F a b) (fun r => r.val M = zFE2 (a.val M) (b.val M)) := by
  unfold zF2
  refine hs_bind (hs_g2Mul _ _ _) fun ab hab => hs_bind (hs_g2Lin _ _ _ _) fun u1 hu1 =>
    hs_bind (hs_g2Lin _ _ _ _) fun u2 hu2 => hs_mono (hs_g2Lin _ _ _ _) fun r hr => ?_
  rw [hr, hu2, hu1, hab, hF.z2, zFE2]
  ring

theorem zFE2_sel {l : ℕ} (hl : l < 4) :
    zFE2 ((selPtF l 2 : List FE2).getD 0 0) ((selPtF l 2 : List FE2).getD 1 0) = FE2.ofK (zK l) := by
  have h2 : ∀ x : FE2, x + x = 0 := fe2_add_self
  have hk : ∀ a b : FK, FE2.ofK (a + b) = FE2.ofK a + FE2.ofK b := fun a b => map_add FE2.ofKRingHom a b
  interval_cases l <;> simp [selPtF, zFE2, hk]
  · linear_combination h2 (FE2.ofK (zK 0))
  · linear_combination h2 (FE2.ofK (zK 0))
  · linear_combination 2 * h2 (FE2.ofK (zK 0)) + h2 (FE2.ofK (zK 1)) + h2 (FE2.ofK (zK 2))

/-- **A `D` half's tail in the circuit's form** (`mass·zF`) is `tailDE2`'s. -/
theorem tailD_val (r : List FE2) (hr : r.length = 20) {l : ℕ} (hl : l < 4) :
    (1 + kapE (r ++ selPtF l 2)) * zFE2 ((r ++ selPtF l 2).getD 20 0) ((r ++ selPtF l 2).getD 21 0) =
      tailMassE2 r * zStarE2 l := by
  have g : ∀ i < 2, (r ++ (selPtF l 2 : List FE2)).getD (20 + i) 0 = (selPtF l 2 : List FE2).getD i 0 := by
    intro i _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hr, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  have g' : ∀ i < 20, (r ++ (selPtF l 2 : List FE2)).getD i 0 = r.getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  rw [g 0 (by norm_num), g 1 (by norm_num), zFE2_sel hl, kapE, g' 18 (by norm_num), g' 19 (by norm_num),
    tailMassE2, zStarE2, zStarF_c0, fe2_sub, fe2_sub, fe2_sub]

/-! ## The preparation of each claim kind -/

section Prep

variable {F : FCtx} {s sK : Cell} {b : Bool}

theorem fe_sub (a t : FE) : a - t = a + t := CharTwo.sub_eq_add a t

theorem prepZ_e3 (hF : FCtxOk M F) (hs : s.val M = if b then 1 else 0) (cc : CClaim)
    (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b (.e3 cc) cl) :
    Hs c M (prepZ F s sK (.e3 cc)) (fun r => SRel M s r (scOf b cl)) := by
  obtain ⟨⟨-, hwf, hbc⟩, hzw, ht⟩ := hr
  show Hs c M (zClaimG s F.z F.o cc >>= fun r => pure (PF.e3 r.1 r.2, r.1.value)) _
  refine hs_bind (zClaimG_spec hF.z hF.o cc hzw) fun r hZ => hs_pure (srel_mk hs ?_ ?_ ?_ ?_)
  · exact ⟨hZ.wf hwf, fun h2 => by rw [hZ.reg h2]; exact hZ.regC h2⟩
  · show r.1.value.val M = _
    rw [hZ.value, hs]
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, scOf, hbc, BlockClaim.onStack, cval_value]
    · simp only [if_true, one_mul, scOf, onStackZB, hbc, ht rfl, cval_value, fe_sub]
  · intro hb x hx
    subst hb
    show (r.1.val M).2.onStack.1 x = (scOf false cl).1 x
    simp only [scOf, Bool.false_eq_true, if_false, hbc]
    by_cases h2 : r.2 = true
    · rw [hZ.reg h2]
    · exact hZ.big (by simpa using h2) (by rw [hs]; rfl) x hx
  · intro hb x hx
    subst hb
    have hsm := hZ.small (by rw [hs]; rfl) x hx
    simp only [scOf, if_true, hbc, ht]
    rw [← hsm]
    by_cases h2 : r.2 = true
    · rw [if_pos h2, ← hZ.reg h2]
      simp only [pfWS, h2, if_true]
    · rw [if_neg h2]
      simp only [pfWS, h2, Bool.false_eq_true, ite_false]

theorem prepZ_half (hs : s.val M = if b then 1 else 0) (h : Bool) (parts : List (C2 × Placement × List C2)) (v : Cell)
    (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b (.half h parts v) cl) :
    Hs c M (prepZ F s sK (.half h parts v)) (fun r => SRel M s r (scOf b cl)) := by
  obtain ⟨⟨-, hp, hbc⟩, hreg, ht⟩ := hr
  refine hs_pure (srel_mk hs (fun e he => ⟨(hp e he).1, (hp e he).2.1, (hp e he).2.2.1, by
    simp only [if_true]; exact hreg e he⟩) ?_ ?_ ?_)
  · cases b
    · simp only [scOf, Bool.false_eq_true, if_false, hbc] <;> rfl
    · simp only [scOf, if_true, onStackZB, hbc, ht, sub_zero] <;> rfl
  · intro hb x hx
    subst hb
    simp only [scOf, Bool.false_eq_true, if_false, hbc]
    rw [halfB_parts h _ _ x hx]
    simp only [one_mul]
    rfl
  · intro hb x hx
    subst hb
    simp only [scOf, if_true, hbc, ht]
    rw [halfB_small h _ (fun e he => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact hreg e' he') _ 0 x hx]
    rfl

theorem prepZ_row (hs : s.val M = if b then 1 else 0) (blk : Placement) (z : List C2) (nu : RowNu) (v : Cell)
    (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b (.row blk z nu v) cl) :
    Hs c M (prepZ F s sK (.row blk z nu v)) (fun r => SRel M s r (scOf b cl)) := by
  obtain ⟨⟨-, eqR, hnu, hne, hzK, hzl, hvc, hbc⟩, hreg, ht⟩ := hr
  have hok : PFOk (PF.row blk z none nu true) := ⟨hne, hzK, (by intro _ h; cases h), hzl, hvc, fun _ => hreg⟩
  refine hs_pure (srel_mk hs hok ?_ ?_ ?_)
  · cases b
    · simp only [scOf, Bool.false_eq_true, if_false, hbc] <;> rfl
    · simp only [scOf, if_true, onStackZB, hbc, ht, sub_zero] <;> rfl
  · intro hb x hx
    subst hb
    simp only [scOf, Bool.false_eq_true, if_false, hbc]
    show blk.eqAbove x * rowLV M nu z none (x.take blk.variableCount) = _
    rw [rowLV_none nu eqR hnu]
    simp only [BlockClaim.onStack]
  · intro hb x hx
    subst hb
    simp only [scOf, if_true, hbc, ht]
    rw [onStackZB_reg _ 0 hreg x hx]
    show (shiftP blk).eqAbove (rotZ x) * rowLV M nu z none ((rotZ x).take blk.variableCount) = _
    rw [rowLV_none nu eqR hnu]
    simp only [shiftB, BlockClaim.onStack, shiftP_vc]

theorem prepZ_dhalf (hF : FCtxOk M F) (hs : s.val M = if b then 1 else 0) (hsK : sK.val M = if b then 1 else 0)
    (h : Bool) (zl : List C2) (v : Cell) (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b (.dhalf h zl v) cl) :
    Hs c M (prepZ F s sK (.dhalf h zl v)) (fun r => SRel M s r (scOf b cl)) := by
  obtain ⟨⟨-, hzK, hzl, -, hbc⟩, r, l, hl4, hrl, hzv, ht⟩ := hr
  have hs2 := sK2_val hF hsK
  show Hs c M (kappa2 F zl >>= fun κ => muxD F sK zl κ >>= fun mz => g2One κ >>= fun mass =>
    zF2 F (zl.getD 20 default) (zl.getD 21 default) >>= fun zf => g2Mul mass zf F.z2 >>= fun t =>
    mulAdd .K sK (if h then t.im else t.re) v >>= fun v' =>
    pure (PF.half h [(mz.1, ⟨22, 0⟩, mz.2.take 22)] false, v')) _
  refine hs_bind (kappa2_spec hF zl (by omega)) fun κ ⟨_, hκv⟩ =>
    hs_bind (muxD_spec hF hs2 zl (by omega) hzK κ) fun mz ⟨hm1K, hm2K, hmlen, hm1, hm2⟩ =>
    hs_bind (hs_g2One κ) fun mass hmass => hs_bind (zF2_spec hF _ _) fun zf hzf =>
    hs_bind (hs_and (hs_g2Mul mass zf F.z2) (g2Mul_K _ _ _)) fun t ⟨htv, htK⟩ =>
    hs_bind (hs_mulAdd _ _ _ _) fun v' hv' => hs_pure (srel_mk hs ?_ ?_ ?_ ?_)
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    refine ⟨hm1K, fun x hx => hm2K x (List.mem_of_mem_take hx), by simp [hmlen, hzl], ?_⟩
    show (22 : ℕ) ≤ CMain.nu20
    decide
  · have hT : t.val M = tailMassE2 r * zStarE2 l := by
      rw [htv, hmass, hzf, hF.z2, add_zero, c2_getD zl (by omega), c2_getD zl (by omega), hκv, hzv]
      exact tailD_val r hrl hl4
    have hcell : (if h then t.im else t.re).val M = FE.ofK (if h then (t.val M).im else (t.val M).re) := by
      cases h
      · exact (kcell_val htK.1).symm
      · exact (kcell_val htK.2).symm
    have htail : cl.2.2 = FE.ofK (if h then (tailMassE2 r * zStarE2 l).im else (tailMassE2 r * zStarE2 l).re) := by
      rw [ht]; cases h <;> rfl
    show v'.val M = _
    rw [hv', hsK, hcell, hT]
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_mul, zero_add, scOf, hbc]; rfl
    · simp only [if_true, one_mul, scOf, onStackZB, hbc, htail, fe_sub]
      rw [add_comm]; rfl
  · intro hb x hx
    subst hb
    simp only [Bool.false_eq_true, if_false] at hm1 hm2
    simp only [scOf, Bool.false_eq_true, if_false, hbc]
    rw [halfB_parts h _ _ x hx]
    show ((partsV M [(mz.1, ⟨22, 0⟩, mz.2.take 22)]).map fun e => (partH h e).onStack.1 x).sum = _
    simp only [partsV, List.map_cons, List.map_nil, one_mul]
    rw [hm1, List.map_take, hm2, List.take_of_length_le (by simp [hzl])]
  · intro hb x hx
    subst hb
    simp only [if_true] at hm1 hm2
    have hzl' : (zl.map (C2.val M)).length = 22 := by simp [hzl]
    simp only [scOf, if_true, hbc]
    rw [halfD_small h _ hzl' _ _ x hx]
    show ((partsV M [(mz.1, ⟨22, 0⟩, mz.2.take 22)]).map fun e => (partH h e).onStack.1 (rotZ x)).sum = _
    simp only [partsV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, partH,
      BlockClaim.onStack]
    rw [hm1, hκv, List.map_take, hm2]
    have ed : ((zl.map (C2.val M)).take 18 ++ [(zl.map (C2.val M)).getD 20 0, (zl.map (C2.val M)).getD 21 0, 0, 0] ++
        (zl.map (C2.val M)).drop 22).take 22 = dzE (zl.map (C2.val M)) := by
      rw [List.drop_of_length_le (by omega), List.append_nil, dzE]
      exact List.take_of_length_le (by simp [hzl'])
    rw [ed]

theorem rowLV_congr (nu : RowNu) {zs zs' : List C2} (h : zs.map (C2.val M) = zs'.map (C2.val M)) (κ : Option C2)
    (y : List FE) : rowLV M nu zs κ y = rowLV M nu zs' κ y := by
  unfold rowLV; rw [h]

theorem kapE_take (zv : List FE2) : kapE (zv.take 22) = kapE zv := by
  simp only [kapE, List.getD_eq_getElem?_getD, List.getElem?_take]
  simp

theorem prepZ_drow (hF : FCtxOk M F) (hs : s.val M = if b then 1 else 0) (hsK : sK.val M = if b then 1 else 0)
    (zl : List C2) (nu : RowNu) (v : Cell) (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b (.drow zl nu v) cl) :
    Hs c M (prepZ F s sK (.drow zl nu v)) (fun r => SRel M s r (scOf b cl)) := by
  obtain ⟨⟨-, eqR, hnu, hne, hzK, hzl, -, hbc⟩, h22, eqR', hnu', ht⟩ := hr
  have hs2 := sK2_val hF hsK
  have hzl' : zl.length = 23 := hzl
  show Hs c M (kappa2 F zl >>= fun κ => muxD F sK zl κ >>= fun mz => rowTailG F nu zl κ >>= fun tl =>
    mulAdd .E s tl v >>= fun v' => pure (PF.row ⟨CMain.nu20, 0⟩ mz.2 (some mz.1) nu false, v')) _
  refine hs_bind (kappa2_spec hF zl (by omega)) fun κ ⟨_, hκv⟩ =>
    hs_bind (muxD_spec hF hs2 zl (by omega) hzK κ) fun mz ⟨hm1K, hm2K, hmlen, hm1, hm2⟩ =>
    hs_bind (rowTailG_spec hF nu eqR' hnu' zl hzl' κ hκv) fun tl htl =>
    hs_bind (hs_mulAdd _ _ _ _) fun v' hv' => hs_pure (srel_mk hs ?_ ?_ ?_ ?_)
  · have hne' : mz.2 ≠ [] := by
      intro e
      have h0 := hmlen
      rw [e, List.length_nil, hzl'] at h0
      omega
    have hk : ∀ cκ, some mz.1 = some cκ → KC2 cκ := by intro cκ e; cases e; exact hm1K
    exact ⟨hne', hm2K, hk, by rw [hmlen, hzl'], le_refl _, fun h => by cases h⟩
  · show v'.val M = _
    rw [hv', hs, htl]
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_mul, zero_add, scOf, hbc]; rfl
    · simp only [if_true, one_mul, scOf, onStackZB, hbc, ht, fe_sub]
      rw [add_comm]
  · intro hb x hx
    subst hb
    simp only [Bool.false_eq_true, if_false] at hm1 hm2
    simp only [scOf, Bool.false_eq_true, if_false, hbc]
    show (⟨CMain.nu20, 0⟩ : Placement).eqAbove x * rowLV M nu mz.2 (some mz.1) (x.take CMain.nu20) = _
    rw [rowLV_congr nu hm2, rowLV_one nu eqR hnu zl _ mz.1 hm1]
    simp only [BlockClaim.onStack]
  · intro hb x hx
    subst hb
    simp only [if_true] at hm1 hm2
    have hzv : (zl.map (C2.val M)).length = 23 := by simp [hzl']
    simp only [scOf, if_true, hbc]
    rw [rowZ_small eqR _ hzv h22 _ _ x hx]
    show (⟨CMain.nu20, 0⟩ : Placement).eqAbove (rotZ x) * rowLV M nu mz.2 (some mz.1) ((rotZ x).take CMain.nu20) = _
    have hrx : (rotZ x).length = CMain.nu20 := rotZ_length x hx
    rw [eqAbove_top _ _ hrx, one_mul, List.take_of_length_le (by omega), rowLV]
    refine sum_congr rfl fun k hk => ?_
    rw [Lnu_eq nu eqR hnu (mem_range.mp hk)]
    refine congrArg _ ?_
    have hmzl : (mz.2.map (C2.val M)).length = 23 := by simp [hmlen, hzl']
    have hg22 : ((mz.2.map (C2.val M)).map (zk k)).getD 22 0 = 0 := by
      rw [getD_map_zk, hm2]
      have : ((zl.map (C2.val M)).take 18 ++ [(zl.map (C2.val M)).getD 20 0, (zl.map (C2.val M)).getD 21 0, 0, 0] ++
          (zl.map (C2.val M)).drop 22).getD 22 0 = (zl.map (C2.val M)).getD 22 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp [List.getD_eq_getElem?_getD, hzl']
      rw [this, h22, zk_zero]
    rw [pR_last _ (by simp [hmlen, hzl']) hg22 _ (by rw [hrx]), ← List.map_take, hm2]
    have ed : ((zl.map (C2.val M)).take 18 ++ [(zl.map (C2.val M)).getD 20 0, (zl.map (C2.val M)).getD 21 0, 0, 0] ++
        (zl.map (C2.val M)).drop 22).take 22 = dzE ((zl.map (C2.val M)).take 22) := by
      rw [List.take_append_of_le_length (by simp; omega), dzE, List.take_take]
      simp [List.getD_eq_getElem?_getD]
    rw [ed, kapK, hm1, hκv, kapE_take]
    ring

end Prep

/-! ## The pin in both shapes -/

theorem eqEval_rotZ (a b : List FE) (h : a.length = b.length) (ha : a ≠ []) :
    eqEval (rotZ a) (rotZ b) = eqEval a b := by
  match a, b, h, ha with
  | [], _, _, ha => exact absurd rfl ha
  | _ :: _, [], h, _ => simp at h
  | a0 :: as, b0 :: bs, h, _ =>
  simp only [rotZ, List.tail_cons, List.headD_cons]
  rw [Shape.eqEval_append (by simpa using h), Shape.eqEval_cons, Shape.eqEval_cons, Shape.eqEval_nil_left]
  ring

theorem cell_getD (z : List Cell) {i : ℕ} (hi : i < z.length) :
    (z.getD i default).val M = (z.map (Cell.val M)).getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem pinZG_spec {s : Cell} {b : Bool} (hs : s.val M = if b then 1 else 0) (pin : CClaim)
    (hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (pinPt pin)) (hl : (pinPt pin).length = CMain.nu20) :
    Hs c M (pinZG s pin) (fun r => SRel M s (PF.e3 r.1 false, r.1.value) ((pin.val M).2.weight, (pin.val M).2.value)) := by
  unfold pinZG
  refine hs_bind (hs_mapBC _ (fun i => mux (s.val M) (((pinPt pin).getD i default).val M)
    (((pinPt pin).getD ((i + 1) % CMain.nu20) default).val M)) (List.range CMain.nu20) fun i _ => muxG_spec _ _ _)
    fun z' hz' => hs_pure (srel_mk hs ?_ ?_ ?_ ?_)
  · have hzl : z'.length = CMain.nu20 := by simpa using congrArg List.length hz'
    refine ⟨?_, fun h => by cases h⟩
    simp [WF1, hzl]
  · show pin.value.val M = _
    rw [cval_value]
  · have epin : (pin.val M).2 = BlockClaim.point ⟨CMain.nu20, 0⟩ (vs M (pinPt pin)) (pin.value.val M) := by
      simp only [CClaim.val, hpt]
    intro hb x hx
    subst hb
    simp only [Bool.false_eq_true, if_false] at hs
    rw [epin]
    show (⟨CMain.nu20, 0⟩ : Placement).eqAbove x * eqEval (vs M z') (x.take CMain.nu20) = eqEval (vs M (pinPt pin)) x
    rw [eqAbove_top _ _ hx, one_mul, List.take_of_length_le (by omega)]
    congr 1
    rw [vs, hz', vs]
    apply List.ext_getElem (by simp [hl])
    intro i h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, hs, mux_zero]
    rw [cell_getD _ (by omega), List.getD_eq_getElem _ _ (by simpa [hl] using h1), List.getElem_map]
  · have epin : (pin.val M).2 = BlockClaim.point ⟨CMain.nu20, 0⟩ (vs M (pinPt pin)) (pin.value.val M) := by
      simp only [CClaim.val, hpt]
    intro hb x hx
    subst hb
    simp only [if_true] at hs
    rw [epin]
    have hrx : (rotZ x).length = CMain.nu20 := rotZ_length x hx
    show (⟨CMain.nu20, 0⟩ : Placement).eqAbove (rotZ x) * eqEval (vs M z') ((rotZ x).take CMain.nu20) =
      eqEval (vs M (pinPt pin)) x
    rw [eqAbove_top _ _ hrx, one_mul, List.take_of_length_le (by omega)]
    have hvl : (vs M (pinPt pin)).length = CMain.nu20 := by simp [vs, hl]
    have ez : vs M z' = rotZ (vs M (pinPt pin)) := by
      rw [vs, hz']
      apply List.ext_getElem (by simp [rotZ_length _ hvl])
      intro i h1 _
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, hs, mux_one]
      rw [← List.getD_eq_getElem _ 0, rotZ_getD _ hvl h1, cell_getD _ (by rw [hl]; exact Nat.mod_lt _ (by decide))]
      rfl
    rw [ez, eqEval_rotZ _ _ (by rw [hvl, hx]) (by intro e; rw [e] at hvl; simp at hvl)]

/-! ## All claims -/

theorem prepZ_spec {F : FCtx} (hF : FCtxOk M F) {s sK : Cell} {b : Bool} (hs : s.val M = if b then 1 else 0)
    (hsK : sK.val M = if b then 1 else 0) (fc : FClaim) (cl : Com × BlockClaim × FE) (hr : FRelZ M F.z b fc cl) :
    Hs c M (prepZ F s sK fc) (fun r => SRel M s r (scOf b cl)) := by
  cases fc with
  | e3 cc => exact prepZ_e3 hF hs cc cl hr
  | half h parts v => exact prepZ_half hs h parts v cl hr
  | dhalf h z v => exact prepZ_dhalf hF hs hsK h z v cl hr
  | row blk z nu v => exact prepZ_row hs blk z nu v cl hr
  | drow z nu v => exact prepZ_drow hF hs hsK z nu v cl hr

theorem prepZs_spec {F : FCtx} (hF : FCtxOk M F) {s sK : Cell} {b : Bool} (hs : s.val M = if b then 1 else 0)
    (hsK : sK.val M = if b then 1 else 0) : ∀ (cs : List FClaim) (cls : List (Com × BlockClaim × FE)),
    List.Forall₂ (FRelZ M F.z b) cs cls →
    Hs c M (prepZs F s sK cs) (fun rs => List.Forall₂ (fun r cl => SRel M s r (scOf b cl)) rs cls)
  | [], [], _ => hs_pure .nil
  | fc :: cs, cl :: cls, .cons h hrs => by
    unfold prepZs
    exact hs_bind (prepZ_spec hF hs hsK fc cl h) fun r hr =>
      hs_bind (prepZs_spec hF hs hsK cs cls hrs) fun rs hrs' => hs_pure (.cons hr hrs')


end Lvm.Q2
