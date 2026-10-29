-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`; revision 4.3's uniform `finPf`,
-- INT-8; track R4h). The 3.x template is `FRVIRFinalsSG.flag_finPf` (`run_cellsOps`, `run_fhOps`,
-- `run_lvsOps`).
import FRSoundness4R4P4

/-!
# The run kit of INT-8's `finPf` (`gFinPf`), relocated

INT-8's `finPf` computes every point family of the group and selects the kind's by kind tables
(`selOps`: a chain of `keep`s), reads the cells' bits through `keep` (`gCellsOpsK`), computes one pad
chain per family (`padsOps`) and checks the kind's exact final zero tail at the end (`gTailOps`). Its
relocated run (`reloc P.S`) reads the final message at `fieldOffOf P.S fFinal` (`fhOps`, `gTailOps`).
This module has the run lemma of each block:

* **`run_selOps`**: the chain leaves candidate `selI sel (n − 1)` (the last `i < n` the table
  selects, else `0`);
* **`run_gCellsOpsK`**: the cells' sum `cellsVal4` (`eq(cell, ρ)` over `nc` coordinates,
  `eqCellK4`);
* **`run_fhOps4`**: `final̂` over the relocated final elements (`fhVal4`, `finV4`);
* **`run_padsOps`**: family `i`'s pad `Π_{x ∈ sf[m_i − 25 ..]} (1 + x)` (`padF4`);
* **`run_gTailOps`**: the tails' flag `tailOk4`;
* **`gLvsOps_4`**: at `seq4` (whose ladder is 3.x's `lvlStar`) the level steps are 3.x's `lvsOps`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Values -/

/-- `selI sel n`: the last `i ≤ n`, `i ≥ 1`, with `sel i`; else `0`. -/
def selI (sel : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if sel (i + 1) then i + 1 else selI sel i

theorem selI_le (sel : ℕ → Bool) : ∀ n, selI sel n ≤ n
  | 0 => le_rfl
  | i + 1 => by
    unfold selI; split_ifs
    · exact le_rfl
    · exact (selI_le sel i).trans (Nat.le_succ i)

/-- `eq(cell, ρ)` over `nc` coordinates, the product from the left (`gCellOpsK`'s). -/
def eqCellK4 (nc : ℕ) (ρ : Array K) (c : ℕ) : K :=
  ((List.range nc).map fun v => if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0).foldl (· * ·) 1

/-- `A + Σ_{k < n} pw·κ′^k·eq(cell_{j+k}, ρ)` (as `gCellsOpsK` accumulates it). -/
def cellsVal4 (nc : ℕ) (ρ : Array K) (kp : F) (cell : ℕ → ℕ) : ℕ → ℕ → F → K → K
  | 0, _, _, A => A
  | n + 1, j, pw, A => cellsVal4 nc ρ kp cell n (j + 1) (pw * kp) (A + K.smulF pw (eqCellK4 nc ρ (cell j)))

/-- `A + Σ_c final[c]·E[c]` over `S`'s final elements (relocated `fhOps`). -/
def fhVal4 (S : Seq) (inp : Input) (E : Array K) : List ℕ → K → K
  | [], A => A
  | c :: cs, A => fhVal4 S inp E cs (A + finV4 S inp c * E.getD c 0)

/-- The pad of family `m`: `Π_{i < pf − (m − 25)} (1 + sf[m − 25 + i])`. -/
def padF4 (sfv : ℕ → K) (pf m : ℕ) : K :=
  ((List.range (pf - (m - 25))).map fun i => 1 + sfv (m - 25 + i)).prod

/-- The final message's bytes from `2^(t − 25)` K elements on (`gTailOps`' read, `S`'s format). -/
def tailBytes4 (S : Seq) (inp : Input) (t : ℕ) : ByteArray :=
  inp.π.extract (fieldOffOf S fFinal + 2 ^ (t - 25) * 32)
    (fieldOffOf S fFinal + 2 ^ (t - 25) * 32 + (2 ^ S.pf - 2 ^ (t - 25)) * 32)

/-- **The tails' flag**: for each `t`, the bytes past `2^(t − 25)` elements are zero when the kind's
`m` is `t`. -/
def tailOk4 (P : FinP) (κ : Kind) (inp : Input) : Bool :=
  P.tails.all fun t => !decide (P.kv.m κ = t) || (tailBytes4 P.S inp t).data.all (· == 0)

theorem foldl_mul_eq {α : Type} (f : α → K) : ∀ (l : List α) (A : K),
    l.foldl (fun a x => a * f x) A = A * (l.map f).prod
  | [], A => by simp
  | x :: l, A => by rw [List.foldl_cons, foldl_mul_eq f l, List.map_cons, List.prod_cons, mul_assoc]

/-! ## The relocation -/

theorem prodKOps_reloc (S : Seq) : ∀ (xs : List Reg) (acc b : ℕ),
    (prodKOps xs acc b).map (reloc S) = prodKOps xs acc b
  | [], _, _ => rfl
  | _ :: xs, _, b => by rw [prodKOps, List.map_cons, prodKOps_reloc S xs]; rfl

theorem srcOp_reloc (S : Seq) (one z0 : Reg) (s : PtSrc) : reloc S (srcOp one z0 s) = srcOp one z0 s := by
  cases s <;> rfl

theorem ptsOps_reloc (S : Seq) (one z0 : Reg) : ∀ (ss : List (List PtSrc)) (b : ℕ),
    (ptsOps one z0 ss b).map (reloc S) = ptsOps one z0 ss b
  | [], _ => rfl
  | s :: ss, b => by
    rw [ptsOps, List.map_append, ptsOps_reloc S one z0 ss, ptOps, List.map_append, List.map_map]
    congr 2
    · exact List.map_congr_left fun x _ => srcOp_reloc S one z0 x

theorem selOps_reloc (S : Seq) (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n pb : ℕ) :
    (selOps sel cand n pb).map (reloc S) = selOps sel cand n pb := by
  rw [selOps, List.map_map]; rfl

theorem gCellsOpsK_reloc (S : Seq) (nc : ℕ) (one g h kp : Reg) (cells : ℕ → KC ℕ) :
    ∀ n j acc pw b, (gCellsOpsK nc one g h kp cells n j acc pw b).map (reloc S) =
      gCellsOpsK nc one g h kp cells n j acc pw b
  | 0, _, _, _, _ => rfl
  | n + 1, j, acc, pw, b => by
    rw [gCellsOpsK, List.map_append, gCellsOpsK_reloc S nc one g h kp cells n, gCellOpsK,
      List.map_append, List.map_append, prodKOps_reloc, List.map_map]
    rfl

theorem gLvsOps_reloc (S S' : Seq) (fi : FinIn) (one cu Ts : Reg) :
    ∀ (ks : List ℕ) (W b : ℕ), (gLvsOps S' fi one cu Ts ks W b).map (reloc S) = gLvsOps S' fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, List.map_append, gLvsOps_reloc S S' fi one cu Ts ks, gLvOps]
    simp only [List.map_append, accOps_reloc, List.map_map, List.map_cons, List.map_nil]
    rfl

theorem padsOps_reloc (S : Seq) (one : Reg) (sf : List Reg) (pf : ℕ) :
    ∀ (ms : List ℕ) (pd : ℕ), (padsOps one sf pf ms pd).map (reloc S) = padsOps one sf pf ms pd
  | [], _ => rfl
  | m :: ms, pd => by
    rw [padsOps, List.map_append, padsOps_reloc S one sf pf ms, padOps, List.map_append,
      prodKOps_reloc, List.map_map]
    rfl

/-- `seq4`'s levels have 3.x's fold rounds `ell` (revision 4.4.1 changes level 4's cap only). -/
theorem seq4_ell_star (k : ℕ) : (seq4.lv k).ell = (lvlStar k).ell := by
  unfold Seq.lv Seq.lvK lvlStar lvl
  rw [seq4_eq]
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | _ + 5 => rfl

/-- At `seq4` the level steps are 3.x's (they read only the levels' `ell`, `seq4_ell_star`). -/
theorem gLvsOps_4 (fi : FinIn) (one cu Ts : Reg) : ∀ (ks : List ℕ) (W b : ℕ),
    gLvsOps seq4 fi one cu Ts ks W b = lvsOps fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, lvsOps, gLvsOps_4 fi one cu Ts ks]
    simp only [gLvOps, lvOps, gSRegs, sRegs, seq4_ell_star]

/-! ## The blocks' runs -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **`selOps`**: the chain of `keep`s leaves the selected candidate. -/
theorem run_selOps (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n : ℕ) (R : Array Val)
    (hc : ∀ i < n, cand i < R.size) :
    ∃ M, pureRun impl κ inp (selOps sel cand n R.size) R [] = some (M, true) ∧ M.length = n - 1 ∧
      (0 < n → selOut cand n R.size < R.size + M.length ∧
        rd (R ++ M.toArray) (selOut cand n R.size) = rd R (cand (selI (fun i => sel i κ) (n - 1)))) := by
  set s : ℕ → Bool := fun i => sel i κ
  set g : ℕ → Op := fun i => .keep (sel (i + 1)) (cand (i + 1)) (if i = 0 then cand 0 else R.size + (i - 1))
  have key : ∀ k, k ≤ n - 1 → pureRun impl κ inp ((List.range k).map g) R [] =
      some ((List.range k).map (fun i => rd R (cand (selI s (i + 1)))), true) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, pureRun_append, ih (by omega), Option.bind_some,
        List.map_singleton]
      have hv : evalOp impl κ inp (R ++ ((List.range k).map (fun i => rd R (cand (selI s (i + 1))))).toArray)
          (g k) = .vals [rd R (cand (selI s (k + 1)))] true := by
        simp only [g, evalOp]
        rw [rd_app_left _ _ (hc (k + 1) (by omega))]
        congr 2
        by_cases hk0 : k = 0
        · subst hk0
          rw [if_pos rfl, rd_app_left _ _ (hc 0 (by omega))]
          simp only [selI, s]; split_ifs <;> rfl
        · rw [if_neg hk0, rd_app]
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [show k' + 1 - 1 = k' by omega, List.getD_eq_getElem _ _ (by simp), List.getElem_map,
            List.getElem_range]
          conv_rhs => rw [selI]
          simp only [s]; split_ifs <;> rfl
      simp only [pureRun, hv, Option.map_some, Bool.and_true, List.map_append, List.map_cons,
        List.map_nil]
  refine ⟨_, key (n - 1) le_rfl, by simp, fun hn => ?_⟩
  simp only [List.length_map, List.length_range]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have h0 := hc 0 (by omega)
    simp only [selOut, le_refl, if_true, selI, Nat.sub_self, List.range_zero, List.map_nil]
    exact ⟨by omega, by rw [show (([] : List Val).toArray) = #[] from rfl, Array.append_empty]⟩
  · have hlt : n - 2 < (List.map (fun i => rd R (cand (selI s (i + 1)))) (List.range (n - 1))).length := by
      simp only [List.length_map, List.length_range]; omega
    rw [selOut, if_neg (by omega), rd_app, List.getD_eq_getElem _ _ hlt, List.getElem_map,
      List.getElem_range, show n - 2 + 1 = n - 1 by omega]
    refine ⟨?_, rfl⟩
    exact Nat.add_lt_add_left (show n - 2 < n - 1 by omega) _

theorem foldl_selK (r : Array Val) (nc : ℕ) (ρ : Array K) (b : ℕ) (c : ℕ)
    (hv : ∀ v < nc, (rd r (b + v)).toK = if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0) :
    ((List.range nc).map (b + ·)).foldl (fun a x => a * (rd r x).toK) 1 = eqCellK4 nc ρ c := by
  rw [eqCellK4, foldl_mul_eq, List.map_map]
  have : ∀ (l : List K) (A : K), l.foldl (· * ·) A = A * l.prod := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => intro A; rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]
  rw [this]
  congr 2
  exact List.map_congr_left fun v hv' => hv v (List.mem_range.1 hv')

/-- The register of `gCellsOpsK`'s last power `pw·κ′ⁿ` (`pw` itself after no cell). -/
def gCellsPwK (nc : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, pw, _ => pw
  | n + 1, _, b => gCellsPwK nc n (b + (2 * nc + 2)) (b + (2 * nc + 3))

/-- With `pw` just below the chain, its last power sits at the chain's last register. -/
theorem gCellsPwK_eq (nc : ℕ) : ∀ (n pw : ℕ), gCellsPwK nc n pw (pw + 1) = pw + 1 + (2 * nc + 3) * n - 1
  | 0, pw => by simp [gCellsPwK]
  | n + 1, pw => by
    rw [gCellsPwK, show pw + 1 + (2 * nc + 3) = pw + 1 + (2 * nc + 2) + 1 by omega, gCellsPwK_eq nc n]
    rw [Nat.mul_succ]; omega

/-- **`gCellsOpsK`** (3.x's `run_cellsOps` with the cells' bits by `keep`); also the last power
register (`gCellsPwK`), from which a second chain continues. -/
theorem run_gCellsOpsK (nc : ℕ) (one g h kp : ℕ) (cells : ℕ → KC ℕ) (ρ : Array K) (kpv : F)
    (r : Array Val) (h1 : one < r.size) (hv1 : rd r one = .k 1) (hk : kp < r.size) (hkv : (rd r kp).toF = kpv)
    (hg0 : ∀ v < nc, g + v < r.size ∧ rd r (g + v) = .k (ρ.getD v 0))
    (hh0 : ∀ v < nc, h + v < r.size ∧ rd r (h + v) = .k (1 + ρ.getD v 0)) (hnc : 0 < nc) :
    ∀ (n j acc pw : ℕ) (A : K) (Pw : F) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    pw < r.size + L.length → (rd (r ++ L.toArray) pw).toF = Pw →
    ∃ M, pureRun impl κ inp (gCellsOpsK nc one g h kp cells n j acc pw (r.size + L.length)) r L =
        some (L ++ M, true) ∧ M.length = (2 * nc + 3) * n ∧
      rd (r ++ (L ++ M).toArray) (gCellsAccK nc n acc (r.size + L.length)) =
        .k (cellsVal4 nc ρ kpv (fun j => cells j κ) n j Pw A) ∧
      (rd (r ++ (L ++ M).toArray) (gCellsPwK nc n pw (r.size + L.length))).toF = Pw * kpv ^ n
  | 0, _, acc, pw, A, Pw, L, _, hA, _, hP =>
    ⟨[], by simp [gCellsOpsK, pureRun], by simp, by simpa [gCellsAccK, cellsVal4] using hA,
      by simpa [gCellsPwK] using hP⟩
  | n + 1, j, acc, pw, A, Pw, L, hacc, hA, hpw, hP => by
    set b := r.size + L.length with hb
    set c := cells j κ
    -- the keeps
    set ks : List Op := (List.range nc).map fun v => .keep (fun κ => (cells j κ).testBit v) (g + v) (h + v)
    set kv : ℕ → Val := fun v => if c.testBit v then .k (ρ.getD v 0) else .k (1 + ρ.getD v 0)
    have h₀ := run_frozen impl κ inp r L (fun op => match op with
      | .keep _ x _ => kv (x - g) | _ => default) ks [] (fun op hop Y => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
        have hv' := List.mem_range.mp hv
        simp only [evalOp, rd_app_left _ _ (hg0 v hv').1, rd_app_left _ _ (hh0 v hv').1, (hg0 v hv').2,
          (hh0 v hv').2, kv, c, Nat.add_sub_cancel_left])
    simp only [List.append_nil] at h₀
    set M₀ := ks.map fun op => match op with | .keep _ x _ => kv (x - g) | _ => default
    have hl₀ : M₀.length = nc := by simp [M₀, ks]
    have hM₀ : ∀ v < nc, rd (r ++ (L ++ M₀).toArray) (b + v) = kv v := by
      intro v hv
      rw [hb, Nat.add_assoc, rd_app, List.getD_append_right _ _ _ _ (by omega)]
      simp [M₀, ks, hv, kv]
    have hR0 : (r ++ (L ++ M₀).toArray).size = b + nc := by simp [hb, hl₀]; omega
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodKOps impl κ inp (r ++ (L ++ M₀).toArray)
      ((List.range nc).map (b + ·)) one 1 []
      (fun x hx => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp hv
        rw [hR0]; omega)
      (by rw [hR0]; simp; omega)
      (by simp [rd_app_left _ _ h1, hv1])
    simp only [List.length_nil, Nat.add_zero, hR0, List.nil_append] at h₁ hv₁
    rw [foldl_selK (r ++ (L ++ M₀).toArray) nc ρ b c (fun v hv => by
      rw [hM₀ v hv]; simp only [kv]; split_ifs <;> rfl),
      prodKOut_eq _ _ _ (by simp; omega)] at hv₁
    have hl₁' : M₁.length = nc := by rw [hl₁]; simp
    have h₁' : pureRun impl κ inp (prodKOps ((List.range nc).map (b + ·)) one (b + nc)) r (L ++ M₀) =
        some (L ++ M₀ ++ M₁, true) := by
      have := pureRun_rebase impl κ inp (prodKOps ((List.range nc).map (b + ·)) one (b + nc)) r (L ++ M₀) []
      rw [List.append_nil] at this; rw [this, h₁]; rfl
    have hv₁' : rd (r ++ (L ++ M₀ ++ M₁).toArray) (b + nc + (nc - 1)) = .k (eqCellK4 nc ρ c) := by
      rw [← hv₁]; simp only [List.length_map, List.length_range]
      rw [show b + nc + nc - 1 = b + nc + (nc - 1) by omega]; simp [Array.append_assoc]
    set e := eqCellK4 nc ρ c
    set u₁ : Val := .k (K.smulF Pw e)
    set u₂ : Val := .k (A + K.smulF Pw e)
    set u₃ : Val := .f (Pw * kpv)
    have hlen1 : r.size + (L ++ M₀ ++ M₁).length = b + 2 * nc := by simp [hb, hl₀, hl₁']; omega
    have e1 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁).toArray) (.mulKF (b + nc + (nc - 1)) pw) =
        .vals [u₁] true := by
      simp only [evalOp]
      rw [hv₁', show L ++ M₀ ++ M₁ = L ++ (M₀ ++ M₁) by simp, FR.rd_pre r hpw, hP]; rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁ ++ [u₁]).toArray) (.addK acc (b + 2 * nc)) =
        .vals [u₂] true := by
      simp only [evalOp]
      rw [← hlen1, rd_new1, show L ++ M₀ ++ M₁ ++ [u₁] = L ++ (M₀ ++ M₁ ++ [u₁]) by simp,
        FR.rd_pre r hacc, hA]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂]).toArray) (.mulF pw kp) =
        .vals [u₃] true := by
      simp only [evalOp]
      rw [show L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] = L ++ (M₀ ++ M₁ ++ [u₁] ++ [u₂]) by simp,
        FR.rd_pre r hpw, hP, rd_app_left _ _ hk, hkv]
    set L' := L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃]
    have hL' : r.size + L'.length = b + (2 * nc + 3) := by
      simp only [L', List.length_append, List.length_singleton]; omega
    obtain ⟨M, hM, hl, hv, hpv⟩ := run_gCellsOpsK nc one g h kp cells ρ kpv r h1 hv1 hk hkv hg0 hh0 hnc n (j + 1)
      (b + (2 * nc + 1)) (b + (2 * nc + 2)) (A + K.smulF Pw e) (Pw * kpv) L' (by rw [hL']; omega)
      (by
        have : b + (2 * nc + 1) = r.size + (L ++ M₀ ++ M₁ ++ [u₁]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [this, show L' = L ++ M₀ ++ M₁ ++ [u₁] ++ (u₂ :: [u₃]) by simp [L'], rd_new])
      (by rw [hL']; omega)
      (by
        have : b + (2 * nc + 2) = r.size + (L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [this, rd_new1]; rfl)
    rw [hL'] at hM hv hpv
    refine ⟨M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M, ?_, by simp [hl, hl₁', hl₀]; ring, ?_, ?_⟩
    · rw [gCellsOpsK, gCellOpsK, List.append_assoc, List.append_assoc, pr_app impl κ inp r (M := M₀) h₀,
        pr_app impl κ inp r (M := M₁) h₁']
      simp only [List.cons_append, List.nil_append]
      rw [show L ++ M₀ ++ M₁ = L ++ M₀ ++ M₁ from rfl, pr_op impl κ inp r e1, pr_op impl κ inp r e2,
        pr_op impl κ inp r e3, show L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃] = L' from rfl, hM]
      simp [L']
    · simp only [gCellsAccK, cellsVal4]
      rw [show L ++ (M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M) = L' ++ M by simp [L']]
      exact hv
    · simp only [gCellsPwK]
      rw [show L ++ (M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M) = L' ++ M by simp [L'], hpv, pow_succ']; ring

/-- **`fhOps`, relocated** (3.x's `run_fhOps` at `S`'s final elements). -/
theorem run_fhOps4 (S : Seq) (r : Array Val) (E : ℕ) (Ev : Array K) (hE : E < r.size) (hEv : (rd r E).toAK = Ev) :
    ∀ (cs : List ℕ) (acc : ℕ) (A : K) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    ∃ M, pureRun impl κ inp ((fhOps E cs acc (r.size + L.length)).map (reloc S)) r L = some (L ++ M, true) ∧
      M.length = 4 * cs.length ∧
      rd (r ++ (L ++ M).toArray) (fhOut cs acc (r.size + L.length)) = .k (fhVal4 S inp Ev cs A)
  | [], acc, A, L, _, hA => ⟨[], by simp [fhOps, pureRun], rfl, by simpa [fhOut, fhVal4] using hA⟩
  | c :: cs, acc, A, L, hacc, hA => by
    set b := r.size + L.length with hb
    set u₁ : Val := .k (finV4 S inp c)
    set u₂ : Val := .k (Ev.getD c 0)
    set u₃ : Val := .k (finV4 S inp c * Ev.getD c 0)
    set u₄ : Val := .k (A + finV4 S inp c * Ev.getD c 0)
    have e1 : evalOp impl κ inp (r ++ L.toArray) (reloc S (.piElemK fFinal (32 * c))) = .vals [u₁] true :=
      (evalOp_reloc impl κ inp _ S (by decide : fFinal < 19) (32 * c) 0 0).2.2.1
    have e2 : evalOp impl κ inp (r ++ (L ++ [u₁]).toArray) (reloc S (.getK E c)) = .vals [u₂] true := by
      simp only [reloc, evalOp, rd_app_left _ _ hE, hEv]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂]).toArray) (reloc S (.mulK b (b + 1))) =
        .vals [u₃] true := by
      have x2 : b + 1 = r.size + (L ++ [u₁]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [reloc, evalOp]
      rw [x2, rd_new1, List.append_assoc, List.singleton_append, rd_new]; rfl
    have e4 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂] ++ [u₃]).toArray) (reloc S (.addK acc (b + 2))) =
        .vals [u₄] true := by
      have x3 : b + 2 = r.size + (L ++ [u₁] ++ [u₂]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [reloc, evalOp]
      rw [x3, rd_new1, List.append_assoc, List.append_assoc, FR.rd_pre r hacc, hA]; rfl
    set L' := L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄]
    have hL' : r.size + L'.length = b + 4 := by
      simp only [L', hb, List.length_append, List.length_singleton]; omega
    obtain ⟨M, hM, hl, hv⟩ := run_fhOps4 S r E Ev hE hEv cs (b + 3) (A + finV4 S inp c * Ev.getD c 0) L'
      (by rw [hL']; omega)
      (by
        have x4 : b + 3 = r.size + (L ++ [u₁] ++ [u₂] ++ [u₃]).length := by
          simp only [hb, List.length_append, List.length_singleton]; omega
        rw [x4, rd_new1])
    rw [hL'] at hM hv
    refine ⟨[u₁, u₂, u₃, u₄] ++ M, ?_, by simp [hl]; ring, ?_⟩
    · rw [fhOps]
      simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r e1, pr_op impl κ inp r e2, pr_op impl κ inp r e3,
        pr_op impl κ inp r e4, show L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄] = L' from rfl, hM]
      simp [L']
    · simp only [fhOut, fhVal4]
      rw [show L ++ ([u₁, u₂, u₃, u₄] ++ M) = L' ++ M by simp [L']]
      exact hv

theorem prod_range_succ_list (f : ℕ → K) (k : ℕ) :
    ((List.range (k + 1)).map f).prod = f 0 * ((List.range k).map fun i => f (i + 1)).prod := by
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]; rfl

/-- **One pad chain** (`padOps` at `μ`, `k` factors, from `pd = R.size`). -/
theorem run_padOps (one : Reg) (sf : List Reg) (sfv : ℕ → K) (μ k : ℕ) (R : Array Val)
    (h1 : one < R.size) (hv1 : rd R one = .k 1)
    (hs : ∀ i < k, sf.getD (μ + i) 0 < R.size ∧ (rd R (sf.getD (μ + i) 0)).toK = sfv (μ + i)) :
    ∃ M, pureRun impl κ inp (padOps one R.size μ k sf) R [] = some (M, true) ∧ M.length = k + (k - 1) ∧
      padReg one R.size k < R.size + M.length ∧
      rd (R ++ M.toArray) (padReg one R.size k) = .k (((List.range k).map fun i => 1 + sfv (μ + i)).prod) := by
  have hB := run_base impl κ inp R ((List.range k).map fun i => Op.addK one (sf.getD (μ + i) 0)) []
    (fun op hop Y => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ h1, rd_app_left _ _ (hs i (List.mem_range.mp hi)).1])
    (fun op hop => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set M₀ : List Val := (List.range k).map fun i => .k (1 + sfv (μ + i))
  have hM₀ : ((List.range k).map fun i => Op.addK one (sf.getD (μ + i) 0)).map (baseVal impl κ inp R) = M₀ := by
    simp only [List.map_map, M₀]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, baseVal, evalOp, hv1, (hs i (List.mem_range.mp hi)).2, toK_k]
  rw [hM₀, List.nil_append] at hB
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨[], by simp [padOps, prodKOps, pureRun], rfl, ?_, ?_⟩
    · simp [padReg]; omega
    · simp [padReg, hv1]
  have hl₀ : M₀.length = k := by simp [M₀]
  have hR0 : (R ++ M₀.toArray).size = R.size + k := by simp [hl₀]
  set xs := (List.range (k - 1)).map (R.size + 1 + ·)
  obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodKOps impl κ inp (R ++ M₀.toArray) xs R.size (1 + sfv μ) []
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := List.mem_range.mp hi
      rw [hR0]; omega)
    (by simp; omega)
    (by
      rw [show (([] : List Val).toArray) = #[] from rfl, Array.append_empty, rd_app0]
      simp [M₀, hk])
  simp only [List.length_nil, Nat.add_zero, hR0, List.nil_append] at h₁ hv₁
  have hfold : xs.foldl (fun a x => a * (rd (R ++ M₀.toArray) x).toK) (1 + sfv μ) =
      ((List.range k).map fun i => 1 + sfv (μ + i)).prod := by
    rw [foldl_mul_eq, show k = (k - 1) + 1 by omega, prod_range_succ_list, Nat.add_zero]
    congr 1
    simp only [xs, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [show R.size + 1 + i = R.size + (i + 1) by omega, rd_app]
    simp [M₀, show i + 1 < k by omega, Nat.add_assoc, toK_k]
  rw [hfold] at hv₁
  have hpr : prodKOut xs R.size (R.size + k) = padReg one R.size k := by
    rw [padReg, if_neg (by omega)]
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; simp [xs, prodKOut]
    · rw [prodKOut_eq _ _ _ (by simp [xs]; omega)]; simp [xs]; omega
  rw [hpr] at hv₁
  refine ⟨M₀ ++ M₁, ?_, by simp [hl₀, hl₁, xs], ?_, ?_⟩
  · rw [padOps]; exact pr_seq impl κ inp hB h₁
  · rw [padReg, if_neg (by omega)]; simp [hl₀, hl₁, xs]; omega
  · rw [← hv₁]; simp [Array.append_assoc]

theorem padsReg_cons (one : Reg) (pf m : ℕ) (ms : List ℕ) (pd i : ℕ) :
    padsReg one pf (m :: ms) pd (i + 1) = padsReg one pf ms (pd + padW pf m) i := by
  simp only [padsReg, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ, Nat.add_assoc]

/-- **The pad chains** (`padsOps`, from `pd = R.size`): family `i`'s product in `padsReg`. -/
theorem run_padsOps (one : Reg) (sf : List Reg) (sfv : ℕ → K) (pf : ℕ) :
    ∀ (ms : List ℕ) (R : Array Val), one < R.size → rd R one = .k 1 →
    (∀ v < pf, sf.getD v 0 < R.size ∧ (rd R (sf.getD v 0)).toK = sfv v) →
    ∃ M, pureRun impl κ inp (padsOps one sf pf ms R.size) R [] = some (M, true) ∧
      M.length = (ms.map (padW pf)).sum ∧ ∀ i < ms.length,
        padsReg one pf ms R.size i < R.size + M.length ∧
        rd (R ++ M.toArray) (padsReg one pf ms R.size i) = .k (padF4 sfv pf (ms.getD i 0))
  | [], R, _, _, _ => ⟨[], by simp [padsOps, pureRun], rfl, fun i hi => absurd hi (by simp)⟩
  | m :: ms, R, h1, hv1, hs => by
    obtain ⟨M₁, h₁, hl₁, hb₁, hv₁⟩ := run_padOps impl κ inp one sf sfv (m - 25) (pf - (m - 25)) R h1 hv1
      (fun i hi => hs _ (by omega))
    have hl₁' : M₁.length = padW pf m := by rw [hl₁, padW]
    obtain ⟨M, hM, hl, hv⟩ := run_padsOps one sf sfv pf ms (R ++ M₁.toArray) (Nat.lt_of_lt_of_le h1 (by simp))
      (by rw [rd_app_left _ _ h1, hv1])
      (fun v hv => ⟨Nat.lt_of_lt_of_le (hs v hv).1 (by simp), by rw [rd_app_left _ _ (hs v hv).1, (hs v hv).2]⟩)
    have hsz : (R ++ M₁.toArray).size = R.size + padW pf m := by simp [hl₁']
    rw [hsz] at hM hv
    refine ⟨M₁ ++ M, ?_, by simp [hl, hl₁'], fun i hi => ?_⟩
    · rw [padsOps, ← hsz]; exact pr_seq impl κ inp h₁ (by rw [hsz]; exact hM)
    · rcases i with _ | i
      · have e : padsReg one pf (m :: ms) R.size 0 = padReg one R.size (pf - (m - 25)) := by
          simp [padsReg]
        rw [e]
        refine ⟨Nat.lt_of_lt_of_le hb₁ (by simp), ?_⟩
        rw [show R ++ (M₁ ++ M).toArray = R ++ M₁.toArray ++ M.toArray by simp [Array.append_assoc],
          rd_append_left (by rw [Array.size_append, List.size_toArray]; exact hb₁), hv₁]
        rfl
      · rw [padsReg_cons]
        obtain ⟨hb, hv'⟩ := hv i (by simpa using hi)
        refine ⟨by
          rw [List.length_append, hl₁', ← Nat.add_assoc]; exact hb, ?_⟩
        rw [show R ++ (M₁ ++ M).toArray = R ++ M₁.toArray ++ M.toArray by simp [Array.append_assoc], hv']
        rfl

/-- **The kind's final zero tails** (relocated `gTailOps`, from `R.size`): the flag is the tails'. -/
theorem run_gTailOps (S : Seq) (P : FinP) : ∀ (ts : List ℕ) (R : Array Val),
    ∃ M, pureRun impl κ inp ((gTailOps (fun _ => P) S.pf ts R.size).map (reloc S)) R [] =
      some (M, ts.all fun t => !decide (P.kv.m κ = t) || (tailBytes4 S inp t).data.all (· == 0))
  | [], _ => ⟨[], rfl⟩
  | t :: ts, R => by
    set u : Val := .b (tailBytes4 S inp t)
    obtain ⟨M, hM⟩ := run_gTailOps S P ts (R ++ [u].toArray)
    have e1 : evalOp impl κ inp (R ++ ([] : List Val).toArray)
        (reloc S (.piField fFinal (2 ^ (t - 25) * 32) ((2 ^ S.pf - 2 ^ (t - 25)) * 32))) = .vals [u] true :=
      (evalOp_reloc impl κ inp _ S (by decide : fFinal < 19) _ _ 0).1
    have hsz : (R ++ [u].toArray).size = R.size + 1 := by simp
    refine ⟨u :: M, ?_⟩
    rw [gTailOps, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.cons_append,
      List.cons_append, List.nil_append, pr_op impl κ inp R e1]
    simp only [pureRun, reloc, evalOp, List.nil_append, rd_app0, List.getD_cons_zero]
    rw [hsz] at hM
    have hM' := pureRun_rebase impl κ inp ((gTailOps (fun _ => P) S.pf ts (R.size + 1)).map (reloc S)) R [u] []
    rw [List.append_nil] at hM'
    rw [List.append_nil, hM', hM]
    simp [u, Val.isZero, List.all_cons]

end Run

end FR.Snd.R4
