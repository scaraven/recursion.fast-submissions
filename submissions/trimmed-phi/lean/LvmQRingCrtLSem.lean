-- New for lvm2 S2GT (GT-C, GT-C2): the looped row-switch leaf's value (blob v4/GT, lever L1: `rowLeafGL`), on GT-L's
-- squaring-loop and `ν` lemmas (`LvmQRingCrtL`: `hs_frobLoop`, `fk_pow_two_pow_64`, `rowNuGL_ok`).
import LvmQRingCrtL

/-!
# The looped row leaf (`rowLeafGL`)

* **`frob_comp`**: the squaring loop's iteration `j < 64` is component `(j + 1) mod 64`: on a `K` cell,
  `a^(2^(j+1)) = a^(2^((j+1) mod 64))` (`fk_pow_two_pow_64`).
* **`comp_iter`**: iteration `j` of the component loop (`compIns`) holds `ν₀(j)·A + ν₁(j)·B`, `(A, B)` the
  `qm`-product of the factors' values read from the squaring loop (`cInit`, `cStep`, `cBody`: `compIns`'s rows).
* **`hs_accLoop`**, **`hs_accLoop2`**: the accumulation loops sum a row of an earlier loop (or `lRhoGL`'s `ν`-pairing)
  over its 64 iterations.
* **`hs_rowLeafGL`**: the leaf is `Σ_k ν₀·A_k + ν₁·B_k` over the components `k` (`crtL`), `ν` read through `nuAt` at
  iteration `(k + 63) mod 64`; **`rowLeafGL_weightN`**: with `RowNuOk` it is V's row weight `rowW`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Finset
open Lvm.Q1 (Ins Src tplOf)

variable {c : Ctx} {M : Mem}

/-- The squaring loop's iteration `j < 64` is component `(j + 1) mod 64`. -/
theorem frob_comp {a : Cell} (ha : a.ty = .K) {j : ℕ} (hj : j < 64) :
    a.val M ^ 2 ^ (j + 1) = a.val M ^ 2 ^ ((j + 1) % 64) := by
  rcases Nat.lt_or_ge (j + 1) 64 with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have h63 : j + 1 = 64 := by (clear * - j hj h; omega)
    rw [h63, Nat.mod_self, pow_zero, pow_one]
    rcases a with ⟨ty, n⟩
    cases ha
    show (FE.ofKRingHom (M.k n)) ^ 2 ^ 64 = FE.ofKRingHom (M.k n)
    rw [← map_pow, fk_pow_two_pow_64]

/-- The `K` version of `frob_comp`. -/
theorem fk_comp (a : FK) {j : ℕ} (hj : j < 64) : a ^ 2 ^ (j + 1) = a ^ 2 ^ ((j + 1) % 64) := by
  rcases Nat.lt_or_ge (j + 1) 64 with h | h
  · rw [Nat.mod_eq_of_lt h]
  · rw [show j + 1 = 64 by (clear * - j hj h; omega), Nat.mod_self, pow_zero, pow_one, fk_pow_two_pow_64]

/-- Summing over the iterations is summing over the components (`c(j) = (j + 1) mod 64` is a rotation). -/
theorem sum_rot64 (f : ℕ → FE) : ∑ j ∈ range 64, f ((j + 1) % 64) = ∑ k ∈ range 64, f k := by
  have h : ∑ j ∈ range 63, f ((j + 1) % 64) = ∑ j ∈ range 63, f (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hj; (clear * - j this; omega))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ' f, h]

/-! ## Loop rows -/

theorem hs_loop_rows (dims : List ℕ) (tpl : List LRow) :
    Hs c M (loop dims tpl) (fun o => o.dims = dims ∧ o.tpl = tpl ∧
      ∀ jf < 2 ^ dims.sum, ∀ t < tpl.length, LRel c M o jf t) :=
  fun _ h => ⟨rfl, rfl, fun _ hjf _ ht => loop_rel h hjf ht⟩

theorem row_muladd {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j t : ℕ} (h : LRel c M o j t)
    (ht : t < ins.length) {τ : Ty} {a b d : Src} (hi : ins.getD t default = ⟨.muladd, τ, [a, b, d]⟩) :
    (o.cell t j).val M = a.toOpd.val M o j * b.toOpd.val M o j + d.toOpd.val M o j := by
  have hr : o.tpl.getD t default = ⟨.muladd, τ, [a.toOpd, b.toOpd, d.toOpd]⟩ := by
    rw [ho, Lvm.Q1.tplOf_getD ins ht, hi]; rfl
  simpa using lrel_muladd hr h

theorem row_lin {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j t : ℕ} (h : LRel c M o j t)
    (ht : t < ins.length) {k k' : FK} {τ : Ty} {a b : Src} (hi : ins.getD t default = ⟨.lin k k', τ, [a, b]⟩) :
    (o.cell t j).val M = a.toOpd.val M o j + FE.ofK k * b.toOpd.val M o j + FE.ofK k' := by
  have hr : o.tpl.getD t default = ⟨.lin k k', τ, [a.toOpd, b.toOpd]⟩ := by
    rw [ho, Lvm.Q1.tplOf_getD ins ht, hi]; rfl
  simpa using lrel_lin hr h

theorem sv_loc (o : LoopOut) {j : ℕ} (hj : j < 2 ^ o.dims.sum) (k : ℕ) :
    (Src.loc k).toOpd.val M o j = (o.cell k j).val M := Opd.val_cur M o hj k

theorem sv_cell (o : LoopOut) (j : ℕ) (x : Cell) : (Src.ext x.addr).toOpd.val M o j = x.val M :=
  Cell.val_opd M o j x

/-- A loop of 64 iterations reads `nuAddr l` at iteration `j` as `nuAt l j`. -/
theorem val_nuAddr (o : LoopOut) (ho : o.dims = [6]) {j : ℕ} (hj : j < 64) (l : List Cell) :
    (Opd.abs (nuAddr l)).val M o j = (nuAt l j).val M :=
  Lvm.Q1.iterXv_ext1 M o ho (by simpa using hj) .E _ _

theorem sv_nu (o : LoopOut) (ho : o.dims = [6]) {j : ℕ} (hj : j < 64) (l : List Cell) :
    (Src.ext (nuAddr l)).toOpd.val M o j = (nuAt l j).val M := val_nuAddr o ho hj l

/-- A loop over an earlier loop's dimensions reads `F.addr i` at iteration `j` as `F`'s cell. -/
theorem sv_addr (P F : LoopOut) (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum) (i : ℕ) :
    (Src.ext (F.addr i)).toOpd.val M P j = (F.cell i j).val M := Opd.val_abs_addr P F hPd hj i

theorem getD_pre {L R ins : List Ins} (h : ins = L ++ R) (i : ℕ) :
    ins.getD (L.length + i) default = R.getD i default := by
  subst h; rw [List.getD_append_right _ _ _ _ (by (clear * - L i; omega)), Nat.add_sub_cancel_left]

/-- **`qmIns`'s rows compute `qm`**: `re` at `t0 + 1`, `im` at `t0 + 4`. -/
theorem qm_rows {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j : ℕ} (hj : j < 2 ^ o.dims.sum)
    (hrel : ∀ t < ins.length, LRel c M o j t) {z : Cell} (hz : z.val M = 0) {tw A B α β : Src} {t0 : ℕ}
    (hseg : ∀ i < 5, ins.getD (t0 + i) default = (qmIns z tw t0 A B α β).getD i default)
    (hlen : t0 + 5 ≤ ins.length) :
    ((o.cell (t0 + 1) j).val M, (o.cell (t0 + 4) j).val M) =
      qm (tw.toOpd.val M o j) (A.toOpd.val M o j, B.toOpd.val M o j) (α.toOpd.val M o j, β.toOpd.val M o j) := by
  have r0 := row_muladd ho (hrel t0 (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 0 (by norm_num))
  have r1 := row_muladd ho (hrel (t0 + 1) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 1 (by norm_num))
  have r2 := row_muladd ho (hrel (t0 + 2) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 2 (by norm_num))
  have r3 := row_muladd ho (hrel (t0 + 3) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 3 (by norm_num))
  have r4 := row_muladd ho (hrel (t0 + 4) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 4 (by norm_num))
  rw [sv_cell, hz, add_zero] at r0 r2
  rw [sv_loc o hj] at r1 r2 r3 r4
  simp only [qm]
  refine Prod.ext ?_ ?_
  · show (o.cell (t0 + 1) j).val M = _
    rw [r1, r0]
  · show (o.cell (t0 + 4) j).val M = _
    rw [r4, r3, r2, r0]
    ring

/-! ## `compIns`'s rows -/

/-- `compIns`'s first rows: factor `0`'s `α` (row `0`) and `β`. -/
def cInit (F : LoopOut) (xb : ℕ) : List Ins × Src × Src :=
  ([⟨.lin 1 1, .E, [.ext (ec xb).addr, .ext (F.addr (2 * 0))]⟩], .loc 0, .ext (F.addr (2 * 0 + 1)))

/-- `compIns`'s step for factor `l`: its `α` row, then `qmIns` (`re` at `ta + 2`, `im` at `ta + 5`). -/
def cStep (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (acc : List Ins × Src × Src) (l : ℕ) :
    List Ins × Src × Src :=
  (acc.1 ++ ⟨.lin 1 1, .E, [.ext (ec (xb + l)).addr, .ext (F.addr (2 * l))]⟩ ::
      qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0))) (acc.1.length + 1) acc.2.1 acc.2.2 (.loc acc.1.length)
        (.ext (F.addr (2 * l + 1))),
    .loc (acc.1.length + 2), .loc (acc.1.length + 5))

/-- `compIns`'s factor rows after `m` steps. -/
def cFold (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (m : ℕ) : List Ins × Src × Src :=
  (List.range m).foldl (fun acc l => cStep F n κ xb z acc (l + 1)) (cInit F xb)

/-- `compIns`'s rows before the last two (the `κ` factor last). -/
def cBody (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) : List Ins × Src × Src :=
  if κ then
    ((cFold F n κ xb z (n - 1)).1 ++ qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0)))
        (cFold F n κ xb z (n - 1)).1.length (cFold F n κ xb z (n - 1)).2.1 (cFold F n κ xb z (n - 1)).2.2
        (.ext (F.addr (2 * n))) (.ext (F.addr (2 * n + 1))),
      .loc ((cFold F n κ xb z (n - 1)).1.length + 1), .loc ((cFold F n κ xb z (n - 1)).1.length + 4))
  else cFold F n κ xb z (n - 1)

theorem compIns_eq (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (a0 a1 : Addr) :
    compIns F n κ xb z a0 a1 = (cBody F n κ xb z).1 ++
      [⟨.muladd, .E, [.ext a0, (cBody F n κ xb z).2.1, .ext z.addr]⟩,
        ⟨.muladd, .E, [.ext a1, (cBody F n κ xb z).2.2, .loc (cBody F n κ xb z).1.length]⟩] := by
  unfold compIns cBody cFold cStep cInit
  cases κ <;> rfl

theorem cFold_succ (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (m : ℕ) :
    cFold F n κ xb z (m + 1) = cStep F n κ xb z (cFold F n κ xb z m) (m + 1) := by
  rw [cFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl

theorem cBody_pre (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) :
    ∃ R, (cBody F n κ xb z).1 = (cFold F n κ xb z (n - 1)).1 ++ R := by
  unfold cBody; cases κ
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨_, rfl⟩

/-- Factor `l`'s value at iteration `j` of the squaring loop `F`: `(1 + a_l^(2^c) + x_l, b_l^(2^c))`. -/
def facF (M : Mem) (F : LoopOut) (xb j l : ℕ) : FE × FE :=
  (1 + (F.cell (2 * l) j).val M + M.e (xb + l), (F.cell (2 * l + 1) j).val M)

/-- **The factor rows**: after `m` steps, the chain holds the `qm`-product of factors `0 … m`. -/
theorem cFold_val {F P : LoopOut} {n : ℕ} {κ : Bool} {xb : ℕ} {z : Cell} {ins : List Ins} (hPt : P.tpl = tplOf ins)
    (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum) (hrel : ∀ t < ins.length, LRel c M P j t)
    (hz : z.val M = 0) : ∀ m, (∃ R, ins = (cFold F n κ xb z m).1 ++ R) →
      (cFold F n κ xb z m).1.length = 1 + 6 * m ∧
      ((cFold F n κ xb z m).2.1.toOpd.val M P j, (cFold F n κ xb z m).2.2.toOpd.val M P j) =
        ((List.range m).map fun l => facF M F xb j (l + 1)).foldl
          (qm ((Src.ext (F.addr (2 * n + if κ then 2 else 0))).toOpd.val M P j)) (facF M F xb j 0)
  | 0, ⟨R, hR⟩ => by
    have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
    have hl0 : 0 < ins.length := by rw [hR]; simp [cFold, cInit]
    have r0 := row_lin hPt (hrel 0 hl0) hl0 (by rw [hR]; rfl)
    refine ⟨rfl, ?_⟩
    simp only [cFold, cInit, List.range_zero, List.map_nil, List.foldl_nil]
    rw [sv_loc P hjP, r0, sv_cell, sv_addr P F hPd hj, sv_addr P F hPd hj]
    simp only [facF, Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul, Nat.add_zero]
    exact Prod.ext (by dsimp only; ring) rfl
  | m + 1, ⟨R, hR⟩ => by
    have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
    rw [cFold_succ] at hR ⊢
    have hR' : ins = (cFold F n κ xb z m).1 ++ ((⟨.lin 1 1, .E, [.ext (ec (xb + (m + 1))).addr,
        .ext (F.addr (2 * (m + 1)))]⟩ :: qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0)))
          ((cFold F n κ xb z m).1.length + 1) (cFold F n κ xb z m).2.1 (cFold F n κ xb z m).2.2
          (.loc (cFold F n κ xb z m).1.length) (.ext (F.addr (2 * (m + 1) + 1)))) ++ R) := by
      rw [hR]; simp only [cStep, List.append_assoc]
    obtain ⟨hl, hv⟩ := cFold_val hPt hPd hj hrel hz m ⟨_, hR'⟩
    have hlen : (cFold F n κ xb z m).1.length + 6 ≤ ins.length := by
      rw [hR', List.length_append, List.length_append]; simp [qmIns]
    have rα := row_lin hPt (hrel (cFold F n κ xb z m).1.length (by (clear * - F n κ xb z m ins P j hl hlen; omega))) (by (clear * - F n κ xb z m ins P j hl hlen; omega))
      (by rw [show (cFold F n κ xb z m).1.length = (cFold F n κ xb z m).1.length + 0 from rfl, getD_pre hR' 0]; rfl)
    have hq := qm_rows (z := z) (t0 := (cFold F n κ xb z m).1.length + 1) hPt hjP hrel hz (fun i hi => by
      rw [show (cFold F n κ xb z m).1.length + 1 + i = (cFold F n κ xb z m).1.length + (1 + i) by (clear * - F n κ xb z m i P ins j; omega),
        getD_pre hR' (1 + i), List.getD_append _ _ _ _ (by simp [qmIns]; (clear * - i F P n κ xb z ins j m hi; omega)), show 1 + i = i + 1 by (clear * - i F P n κ xb z ins j m; omega),
        List.getD_cons_succ]) (by (clear * - hlen; omega))
    refine ⟨by simp only [cStep, List.length_append, List.length_cons, qmIns, List.length_nil]; (clear * - F n κ xb z m P ins j hl; omega), ?_⟩
    simp only [cStep]
    rw [sv_loc P hjP, sv_loc P hjP, show (cFold F n κ xb z m).1.length + 2 = (cFold F n κ xb z m).1.length + 1 + 1 by
      (clear * - F n κ xb z m P ins j; omega), show (cFold F n κ xb z m).1.length + 5 = (cFold F n κ xb z m).1.length + 1 + 4 by (clear * - F n κ xb z m P ins j; omega), hq,
      List.range_succ, List.map_append, List.foldl_append, ← hv]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    congr 2
    · rw [sv_loc P hjP, rα, sv_cell]
      simp only [sv_addr P F hPd hj, Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul]
      ring
    · exact sv_addr P F hPd hj _

/-- **Iteration `j` of the component loop**: its last row is `ν₀(j)·A + ν₁(j)·B`, `(A, B)` the `qm`-product (twist
`F(2n + 2κ)`) of the factors `facF` and, with `κ`, `(F(2n), F(2n + 1))`. -/
theorem comp_iter {F P : LoopOut} {n : ℕ} {κ : Bool} {xb : ℕ} {z : Cell} {a0 a1 : Addr}
    (hPt : P.tpl = tplOf (compIns F n κ xb z a0 a1)) (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum)
    (hrel : ∀ t < (compIns F n κ xb z a0 a1).length, LRel c M P j t) (hz : z.val M = 0) (hn : 1 ≤ n) :
    (P.cell ((compIns F n κ xb z a0 a1).length - 1) j).val M =
      (Src.ext a0).toOpd.val M P j * ((((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0)).1 +
      (Src.ext a1).toOpd.val M P j * ((((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0)).2 := by
  have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
  have he := compIns_eq F n κ xb z a0 a1
  have hlast : (compIns F n κ xb z a0 a1).length - 1 = (cBody F n κ xb z).1.length + 1 := by rw [he]; simp
  have hlen : (cBody F n κ xb z).1.length + 2 = (compIns F n κ xb z a0 a1).length := by rw [he]; simp
  have rA := row_muladd hPt (hrel (cBody F n κ xb z).1.length (by (clear * - F n κ xb z a0 a1 P j hlen; omega))) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))
    (by rw [show (cBody F n κ xb z).1.length = (cBody F n κ xb z).1.length + 0 from rfl, getD_pre he 0]; rfl)
  have rB := row_muladd hPt (hrel ((cBody F n κ xb z).1.length + 1) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))
    (by rw [getD_pre he 1]; rfl)
  rw [sv_cell, hz, add_zero] at rA
  rw [sv_loc P hjP, rA] at rB
  rw [hlast, rB]
  -- the chain's value before the last two rows
  have htw : (Src.ext (F.addr (2 * n + if κ then 2 else 0))).toOpd.val M P j =
      (F.cell (2 * n + if κ then 2 else 0) j).val M := sv_addr P F hPd hj _
  obtain ⟨R0, hR0⟩ := cBody_pre F n κ xb z
  have hpre : ∃ R, compIns F n κ xb z a0 a1 = (cFold F n κ xb z (n - 1)).1 ++ R :=
    ⟨R0 ++ _, by rw [he, hR0, List.append_assoc]⟩
  obtain ⟨-, hv⟩ := cFold_val (κ := κ) hPt hPd hj hrel hz (n - 1) hpre
  rw [htw] at hv
  have hr : List.range n = 0 :: (List.range (n - 1)).map (· + 1) := by
    rw [← List.range_succ_eq_map, Nat.sub_add_cancel hn]
  have hval : (((cBody F n κ xb z).2.1.toOpd.val M P j, (cBody F n κ xb z).2.2.toOpd.val M P j) : FE × FE) =
      (((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0) := by
    rw [hr, List.map_cons, List.cons_append, List.foldl_cons, qm_one, List.foldl_append, List.map_map]
    rw [show ((facF M F xb j) ∘ (· + 1)) = fun l => facF M F xb j (l + 1) from rfl, ← hv]
    cases κ
    · rfl
    · obtain ⟨R1, hR1⟩ : ∃ R1, compIns F n true xb z a0 a1 = (cFold F n true xb z (n - 1)).1 ++
          (qmIns z (.ext (F.addr (2 * n + if true then 2 else 0))) (cFold F n true xb z (n - 1)).1.length
            (cFold F n true xb z (n - 1)).2.1 (cFold F n true xb z (n - 1)).2.2 (.ext (F.addr (2 * n)))
            (.ext (F.addr (2 * n + 1))) ++ R1) :=
        ⟨_, by rw [he]; unfold cBody; simp only [ite_true, List.append_assoc]; exact rfl⟩
      have hq := qm_rows (z := z) (t0 := (cFold F n true xb z (n - 1)).1.length) hPt hjP hrel hz (fun i hi => by
        rw [getD_pre hR1 i, List.getD_append _ _ _ _ (by simp [qmIns]; (clear * - hi; omega))]) (by
          rw [hR1, List.length_append, List.length_append]; simp [qmIns])
      simp only [cBody, ite_true, List.foldl_cons, List.foldl_nil]
      rw [sv_loc P hjP, sv_loc P hjP, hq, sv_addr P F hPd hj, sv_addr P F hPd hj, sv_addr P F hPd hj]
      rfl
  rw [← hval]
  dsimp only
  ring

/-! ## The accumulation loop -/

/-- **The one-row accumulation loop** sums row `t` of a loop `P` over its 64 iterations. -/
theorem hs_accLoop (P : LoopOut) (hPd : P.dims = [6]) (t : ℕ) {z : Cell} (hz : z.val M = 0) :
    Hs c M (loopP [6] (tplOf [⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩]) (fun _ => z))
      (fun S => (S.cell 0 63).val M = ∑ j ∈ range 64, (P.cell t j).val M) := by
  intro p h
  have hrow : (tplOf [(⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩ : Ins)]).getD 0 default =
      ⟨.lin 1 0, .E, [.prev 0, .abs (P.addr t)]⟩ := rfl
  have key : ∀ j < 64, ((loopP [6] (tplOf [⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩]) (fun _ => z) p).1.cell 0 j).val M
      = ∑ i ∈ range (j + 1), (P.cell t i).val M := by
    intro j hj
    induction j with
    | zero =>
      have hr := lrel_lin hrow (loopP_rel h (show 0 < 2 ^ [6].sum by decide) (by simp [tplOf]))
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
      rw [hr, Opd.val_abs_addr _ P (by rw [hPd]; rfl) (by rw [hPd]; decide), show FE.ofK 1 = 1 from rfl,
        show FE.ofK 0 = 0 from rfl, one_mul, add_zero,
        loopP_prev_zero h (by simp [tplOf]) (fun e => by rw [hrow] at e; cases e), hz, zero_add, Finset.sum_range_one]
    | succ j ih =>
      have hj' : j + 1 < 2 ^ [6].sum := by simpa using hj
      have hr := lrel_lin hrow (loopP_rel h hj' (by simp [tplOf]))
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
      rw [hr, Opd.val_abs_addr _ P (by rw [hPd]; rfl) (by rw [hPd]; exact hj'), show FE.ofK 1 = 1 from rfl,
        show FE.ofK 0 = 0 from rfl, one_mul, add_zero, loopP_prev_succ M [6] _ _ p hj', ih (by (clear * - j hj; omega)),
        Finset.sum_range_succ _ (j + 1)]
  exact key 63 (by norm_num)

/-- **The two-row accumulation loop** (`lRhoGL`'s): `Σ_j ν₀(j)·D(0, j) + ν₁(j)·D(1, j)` over the 64 iterations, `ν`
read through `nuAt`. -/
theorem hs_accLoop2 (D : LoopOut) (hDd : D.dims = [6]) (l0 l1 : List Cell) {z : Cell} (hz : z.val M = 0) :
    Hs c M (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z))
      (fun S => (S.cell 1 63).val M = ∑ j ∈ range 64, ((nuAt l0 j).val M * (D.cell 0 j).val M +
        (nuAt l1 j).val M * (D.cell 1 j).val M)) := by
  intro p h
  have h0 : (tplOf [(⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩ : Ins),
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]).getD 0 default =
      ⟨.muladd, .E, [.abs (nuAddr l0), .abs (D.addr 0), .prev 1]⟩ := rfl
  have h1 : (tplOf [(⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩ : Ins),
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]).getD 1 default =
      ⟨.muladd, .E, [.abs (nuAddr l1), .abs (D.addr 1), .cur 0]⟩ := rfl
  have hSd : (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.dims = [6] := rfl
  have step : ∀ j < 64, ((loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.cell 1 j).val M =
      (nuAt l1 j).val M * (D.cell 1 j).val M + ((nuAt l0 j).val M * (D.cell 0 j).val M +
        (Opd.prev 1).val M (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
          ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1 j) := by
    intro j hj
    have hj' : j < 2 ^ [6].sum := by simpa using hj
    have r0 := lrel_muladd h0 (loopP_rel h hj' (by simp [tplOf]))
    have r1 := lrel_muladd h1 (loopP_rel h hj' (by simp [tplOf]))
    simp only [List.getD_cons_zero, List.getD_cons_succ] at r0 r1
    rw [r1, Opd.val_cur M _ (by rw [hSd]; exact hj'), r0, val_nuAddr _ hSd hj, val_nuAddr _ hSd hj,
      Opd.val_abs_addr _ D (by rw [hSd, hDd]) (by rw [hDd]; exact hj'),
      Opd.val_abs_addr _ D (by rw [hSd, hDd]) (by rw [hDd]; exact hj')]
  have key : ∀ j < 64, ((loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.cell 1 j).val M =
      ∑ i ∈ range (j + 1), ((nuAt l0 i).val M * (D.cell 0 i).val M + (nuAt l1 i).val M * (D.cell 1 i).val M) := by
    intro j hj
    induction j with
    | zero =>
      rw [step 0 hj, loopP_prev_zero h (by simp [tplOf]) (fun e => by rw [h1] at e; cases e), hz, add_zero,
        Finset.sum_range_one]
      ring
    | succ j ih =>
      rw [step (j + 1) hj, loopP_prev_succ M [6] _ _ p (by simpa using hj), ih (by (clear * - j hj; omega)),
        Finset.sum_range_succ _ (j + 1)]
      ring
  exact key 63 (by norm_num)

/-! ## The leaf -/

/-- Component `k` of a row leaf's factors: `(1 + z_re^(2^k) + x_l, z_im^(2^k))`, then `κ`'s `(κ_re^(2^k), κ_im^(2^k))`. -/
def crtF (M : Mem) (zs : List C2) (κ : Option C2) (xb k : ℕ) : List (FE × FE) :=
  (List.range zs.length).map (fun l => (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l),
    (zs.getD l default).im.val M ^ 2 ^ k)) ++
  (match κ with
    | some cκ => [(cκ.re.val M ^ 2 ^ k, cκ.im.val M ^ 2 ^ k)]
    | none => [])

/-- Component `k` of a row leaf's product. -/
def crtL (M : Mem) (zs : List C2) (κ : Option C2) (xb k : ℕ) : FE × FE :=
  (crtF M zs κ xb k).foldl (qm (twK k)) (1, 0)

theorem flat2_getD (m : List Cell) (x : Cell) : ∀ (zs : List C2) {l : ℕ}, l < zs.length →
    (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * l) default = (zs.getD l default).re ∧
      (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * l + 1) default = (zs.getD l default).im
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => ⟨rfl, rfl⟩
  | _ :: zs, l + 1, h => by
    have := flat2_getD m x zs (l := l) (by simpa using h)
    rw [show 2 * (l + 1) = 2 * l + 1 + 1 by omega]
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ] using this

theorem flat2_getD_rest (m : List Cell) (x : Cell) (zs : List C2) (i : ℕ) :
    (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * zs.length + i) default = (m ++ [x]).getD i default := by
  have hl : (zs.flatMap (fun c => [c.re, c.im])).length = 2 * zs.length := by
    induction zs with
    | nil => rfl
    | cons y zs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; (clear * - zs; omega)
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by (clear * - zs i hl; omega)), hl, Nat.add_sub_cancel_left]

theorem getD_twist (m : List Cell) (x : Cell) {k : ℕ} (hm : m.length = k) : (m ++ [x]).getD k default = x := by
  rw [List.getD_append_right _ _ _ _ (by (clear * - m k hm; omega)), hm, Nat.sub_self]; rfl

/-- **The looped row leaf** (`rowLeafGL`): `Σ_k ν₀·A_k + ν₁·B_k`, `(A_k, B_k)` component `k`'s product (`crtL`), the
`ν` cells read through `nuAt` at iteration `(k + 63) mod 64`. -/
theorem hs_rowLeafGL (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : ℕ) {z zk : Cell} (hz : z.val M = 0)
    (hzk : zk.val M = 0) (hne : zs ≠ []) (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K)
    (hκ : ∀ cκ, κ = some cκ → cκ.re.ty = .K ∧ cκ.im.ty = .K) :
    Hs c M (rowLeafGL nu zs κ xb z zk) (fun r => r.val M = ∑ k ∈ range 64,
      ((nuAt nu.nu0 ((k + 63) % 64)).val M * (crtL M zs κ xb k).1 +
        (nuAt nu.nu1 ((k + 63) % 64)).val M * (crtL M zs κ xb k).2)) := by
  have hn : 1 ≤ zs.length := by
    rcases zs with _ | ⟨_, _⟩
    · exact absurd rfl hne
    · simp
  unfold rowLeafGL
  refine hs_bind (hs_const .K FK.x zk) fun x hx => ?_
  refine hs_bind (hs_frobLoop hzk _) fun F ⟨hFd, hFv⟩ => ?_
  refine hs_bind (hs_loop_rows _ _) fun P ⟨hPd, hPt, hPrel⟩ => ?_
  refine hs_bind (hs_accLoop P hPd _ hz) fun S hS => hs_pure ?_
  rw [hS]
  -- the factor cells of the squaring loop at iteration `j`, component `(j + 1) mod 64`
  have hfz : ∀ j < 64, ∀ l < zs.length,
      (F.cell (2 * l) j).val M = (zs.getD l default).re.val M ^ 2 ^ ((j + 1) % 64) ∧
      (F.cell (2 * l + 1) j).val M = (zs.getD l default).im.val M ^ 2 ^ ((j + 1) % 64) := by
    intro j hj l hl
    have hKl := hK (zs.getD l default) (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
    rw [hFv (2 * l) (by simp; (clear * - l zs κ j hl; omega)) j hj, hFv (2 * l + 1) (by simp; (clear * - l zs κ j hl; omega)) j hj, (flat2_getD _ _ zs hl).1,
      (flat2_getD _ _ zs hl).2, frob_comp hKl.1 hj, frob_comp hKl.2 hj]
    exact ⟨rfl, rfl⟩
  have htw : ∀ j < 64, (F.cell (2 * zs.length + if κ.isSome then 2 else 0) j).val M = twK ((j + 1) % 64) := by
    intro j hj
    rw [hFv _ (by cases κ <;> simp <;> (clear * - zs j; omega)) j hj, flat2_getD_rest, getD_twist]
    · rw [hx, twK, show FE.ofK FK.x ^ 2 ^ (j + 1) = FE.ofK (FK.x ^ 2 ^ (j + 1)) from
        (map_pow FE.ofKRingHom _ _).symm, fk_comp _ hj]
    · cases κ <;> rfl
  have hkap : ∀ j < 64, ∀ cκ, κ = some cκ →
      (F.cell (2 * zs.length) j).val M = cκ.re.val M ^ 2 ^ ((j + 1) % 64) ∧
      (F.cell (2 * zs.length + 1) j).val M = cκ.im.val M ^ 2 ^ ((j + 1) % 64) := by
    intro j hj cκ e
    subst e
    have h0 := flat2_getD_rest [cκ.re, cκ.im] x zs 0
    have h1 := flat2_getD_rest [cκ.re, cκ.im] x zs 1
    rw [Nat.add_zero] at h0
    rw [hFv _ (by simp; (clear * - zs j; omega)) j hj, hFv _ (by simp; (clear * - zs j; omega)) j hj]
    refine ⟨?_, ?_⟩
    · show (List.getD (zs.flatMap (fun c => [c.re, c.im]) ++ [cκ.re, cκ.im] ++ [x]) (2 * zs.length) default).val M ^ _ = _
      rw [h0]
      exact frob_comp (hκ cκ rfl).1 hj
    · show (List.getD (zs.flatMap (fun c => [c.re, c.im]) ++ [cκ.re, cκ.im] ++ [x]) (2 * zs.length + 1) default).val M ^
        _ = _
      rw [h1]
      exact frob_comp (hκ cκ rfl).2 hj
  -- iteration `j` is component `(j + 1) mod 64`
  have hit : ∀ j < 64,
      (P.cell ((compIns F zs.length κ.isSome xb z (nuAddr nu.nu0) (nuAddr nu.nu1)).length - 1) j).val M =
        (nuAt nu.nu0 j).val M * (crtL M zs κ xb ((j + 1) % 64)).1 +
          (nuAt nu.nu1 j).val M * (crtL M zs κ xb ((j + 1) % 64)).2 := by
    intro j hj
    have hj' : j < 2 ^ F.dims.sum := by rw [hFd]; simpa using hj
    have hPF : P.dims = F.dims := by rw [hPd, hFd]
    rw [comp_iter hPt hPF hj' (fun t ht => hPrel j (by simpa using hj) t (by simpa [tplOf] using ht)) hz hn,
      sv_nu P hPd hj, sv_nu P hPd hj, htw j hj]
    have hl : (List.range zs.length).map (facF M F xb j) ++
        (if κ.isSome then [((F.cell (2 * zs.length) j).val M, (F.cell (2 * zs.length + 1) j).val M)] else []) =
        crtF M zs κ xb ((j + 1) % 64) := by
      unfold crtF
      congr 1
      · refine List.map_congr_left fun l hl => ?_
        have h := hfz j hj l (List.mem_range.mp hl)
        simp only [facF, h.1, h.2]
      · cases κ with
        | none => rfl
        | some cκ =>
          have h := hkap j hj cκ rfl
          simp only [Option.isSome_some, ite_true, h.1, h.2]
    rw [hl]
    rfl
  rw [Finset.sum_congr rfl fun j hj => hit j (Finset.mem_range.mp hj)]
  rw [← sum_rot64 (fun k => (nuAt nu.nu0 ((k + 63) % 64)).val M * (crtL M zs κ xb k).1 +
    (nuAt nu.nu1 ((k + 63) % 64)).val M * (crtL M zs κ xb k).2)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : ((j + 1) % 64 + 63) % 64 = j := by (clear * - j zs hj'; omega)
  simp only [e]

/-- **The looped row leaf is V's row weight** (big shape; `rowLeaf_weightN` for blob v4's `rowLeafGL`): with `ν`'s
cells standing for `eqR` as the loop reads them (`RowNuOk`), the claim point's `E2` coordinates `zs` (`K` cells) and
the basis point's first `|zs|` coordinates in the `E` cells `xb + l`. -/
theorem rowLeafGL_weightN (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) (zs : List C2) (hne : zs ≠ [])
    (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K) (xb : ℕ) (xs : List FE) (hxl : xs.length = zs.length)
    (hx : ∀ l < zs.length, M.e (xb + l) = xs.getD l 0) {z zk : Cell} (hz : z.val M = 0) (hzk : zk.val M = 0) :
    Hs c M (rowLeafGL nu zs none xb z zk) (fun r => r.val M = rowW eqR (zs.map (C2.val M)) xs) := by
  refine hs_mono (hs_rowLeafGL nu zs none xb hz hzk hne hK (fun _ h => by cases h)) fun r hv => ?_
  rw [hv, rowW, sumE_eq, lsum_range,
    show ∑ j ∈ range 128, eqR.getD j 0 * (tensorWD (zs.map (C2.val M)) xs).getD j 0 =
      ∑ j ∈ range 128, (fun j => eqR.getD j 0) j * (tensorWD (zs.map (C2.val M)) xs).getD j 0 from rfl, weight_crt]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hf : ∀ L : List (FE2 × FE), L.foldl (fun P zr => qm (twK k) P (fct k zr)) (1, 0) =
      (L.map (fct k)).foldl (qm (twK k)) (1, 0) := fun L => (List.foldl_map ..).symm
  rw [(hnu.2 k hk').1, (hnu.2 k hk').2, phiA_tensorWD, hf]
  simp only [crtL, crtF, List.append_nil]
  have hzz : (List.zip (zs.map (C2.val M)) xs).map (fct k) = (List.range zs.length).map fun l =>
      (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l), (zs.getD l default).im.val M ^ 2 ^ k) := by
    apply List.ext_getElem
    · simp [hxl]
    · intro l h1 _
      have hl : l < zs.length := by simpa [hxl] using h1
      have hKl := hK _ (List.getElem_mem hl)
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range, fct]
      rw [hx l hl, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by (clear * - l xs M zs xb hxl k hl; omega))]
      have hre : (zs[l]).re.val M = FE.ofK ((zs[l]).re.val M).c₀ := by
        rcases h : zs[l].re with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨rfl, -⟩ := hKl; rfl
      have him : (zs[l]).im.val M = FE.ofK ((zs[l]).im.val M).c₀ := by
        rcases h : zs[l].im with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨-, rfl⟩ := hKl; rfl
      have hp : ∀ a : FK, FE.ofK a ^ 2 ^ k = FE.ofK (a ^ 2 ^ k) := fun a => (map_pow FE.ofKRingHom a _).symm
      rw [hre, him, hp, hp]
      rfl
  rw [hzz]

end Lvm.Q2
