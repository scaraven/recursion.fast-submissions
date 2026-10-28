-- New for `flock-recursive` (BLUEPRINT A.10 rows L1–L3β, §5.2 rows L1–L3; stage S-G7).
import FRSoundnessFrZ

/-!
# L: the per-kind lincheck (positions 68 … 98)

L reduces Zend's pair `(â, b̂)` (claims on `A z`, `B z` at the quirky row point `(λ, r′)`) to one
claim on `z`, per block kind (`FRSpartan` part LinKinds; the matrices are `ZLM`'s):

* **`aStar_bridge`**: Zend's true `Â(λ, r′)` (`bz_final`'s form) is `linAK` at the row weights
  `rowW λ r′_hi` and the block point `r′_blk` (`aStar_eq`, `bStar_eq`).
* L1 (`α` at 68): **`L1Bad`** (`â + α b̂` false), **`l1_single`** (`batch_count`, `1·2^128`).
* L2 (14 rounds from 69, degree 2, `kindExpr 8`): **`D2L`**, **`RejL2`** (a round check fails; round
  0's is `finLc` (i)), **`l2_habs`**, **`l2_single`** (`D2_single`: `2·2^128`), **`rejL2_ok`**.
* L3 (absorb at 97): **`RejLc2`** (`finLc` (ii) fails on the log: L2's last claim is not
  `Σ_j v′_j M̃_j(r_k)` with the kind-masked values `v′ = vM`), **`L3Bad`** (some masked value is not
  `z̄̃_j(r_k)`), **`l3_habs`**.
* L3β (`β` at 98): **`PendLc`** (`v_β` is not `Σ_i β^i t_i` at the true per-kind values `tL`),
  **`l3b_single`** (`batch_count` at 8 values: `7·2^128`, under the kind hypothesis `IndKinds`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

noncomputable section

/-! ## Zend's pair in the lincheck's form -/

theorem ptOf_split {a b : ℕ} (rs : List F) :
    ptOf (a + b) rs = Fin.append (ptOf a rs) (ptOf b (rs.drop a)) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · simp only [Fin.append_left, ptOf, Fin.val_castAdd]
  · simp only [Fin.append_right, ptOf, Fin.val_natAdd, List.getD_eq_getElem?_getD,
      List.getElem?_drop]

theorem pAt_join {q : ℕ} (σ : Fin 64) (h : Fin (2 ^ 8)) (t : Fin (2 ^ q)) :
    pAt σ (join h t).val = join (a := 6) (b := 8) σ h := by
  apply Fin.ext
  simp only [pAt, join]
  have := h.isLt
  omega

theorem div_join {q : ℕ} (h : Fin (2 ^ 8)) (t : Fin (2 ^ q)) : (join h t).val / 256 = t.val := by
  simp only [join]; have := h.isLt; omega

theorem aStar_bridge {ℓ q : ℕ} (hℓ : ℓ = 8 + q) (A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F) (Ind : Fin 9 → ℕ → F)
    (z : ℕ → F) (l : F) (rs : List F) :
    mle (fun u : Fin (2 ^ ℓ) => (skipExt fun σ => ∑ j : Fin 9, Ind j (u.val / 256) *
        ∑ k, A j (pAt σ u.val) k * z (2 ^ 14 * (u.val / 256) + k.val)).eval l) (ptOf ℓ rs) =
      linAK A (fun j t => Ind j t.val) (rowW (p := 8) l (ptOf 8 rs)) (ptOf q (rs.drop 8))
        (fun y : Fin (2 ^ (14 + q)) => z y.val) := by
  subst hℓ
  have ev_sum : ∀ (c : Fin 9 → F) (g : Fin 9 → Fin 64 → F),
      (skipExt fun σ => ∑ j, c j * g j σ).eval l = ∑ j, c j * (skipExt (g j)).eval l := by
    intro c g
    simp only [skipExt_eval, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hR : ∀ T : Fin (2 ^ 14) → F, ∑ k, rowW (p := 8) l (ptOf 8 rs) k * T k =
      ∑ h : Fin (2 ^ 8), eq (ptOf 8 rs) (cube h) *
        (skipExt fun i => T (join (a := 6) (b := 8) i h)).eval l := fun T => rowW_eq (p := 8) l _ T
  rw [ptOf_split, mle_split]
  unfold linAK
  simp only [div_join, pAt_join, mle, ev_sum]
  simp only [hR]
  simp only [join, Fin.val_mk, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset (Fin (2 ^ 8)))) (t := (univ : Finset (Fin (2 ^ q))))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm (s := (univ : Finset (Fin (2 ^ 8)))) (t := (univ : Finset (Fin 9)))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun h _ => ?_
  ring


variable (M : ZLM)

/-- A kind's block bits `q = m − 14`. -/
def qL (κ : Kind) : ℕ := κ.m - 14

theorem mm6_q (κ : Kind) : mm 6 κ = 8 + qL κ := by cases κ <;> rfl

/-- `α` (position 68), the row point's 8 high bits and the block point (Z3's `r′`). -/
def alL (es : Log) : F := fAt es 68 0
def rhiL (es : Log) : Fin 8 → F := ptOf 8 (rZ es)
def rbLc (es : Log) : Fin (qL (kindOf es)) → F := ptOf _ ((rZ es).drop 8)

/-- The indicators as tables on the block cube. -/
def IndF (κ : Kind) (q : ℕ) : Fin 9 → Fin (2 ^ q) → F := fun j t => M.Ind κ j t.val

/-- The quirky row weights `rowW λ r′_hi` (A.8 `rowW`). -/
def rwL (es : Log) : Fin (2 ^ 14) → F := rowW (p := 8) (lamL es) (rhiL es)

/-- **The true `â`, `b̂`** in the lincheck's form (`linAK`). -/
def aLin (L es : Log) : F :=
  linAK M.Ak (IndF M (kindOf es) _) (rwL es) (rbLc es) (zN (kindOf es) L es (qL (kindOf es)))
def bLin (L es : Log) : F :=
  linAK M.Bk (IndF M (kindOf es) _) (rwL es) (rbLc es) (zN (kindOf es) L es (qL (kindOf es)))

theorem aStar_eq (L es : Log) : aStar M L es = aLin M L es :=
  aStar_bridge (mm6_q _) M.Ak (M.Ind (kindOf es)) (zW (kindOf es) L es) _ _

theorem bStar_eq (L es : Log) : bStar M L es = bLin M L es :=
  aStar_bridge (mm6_q _) M.Bk (M.Ind (kindOf es)) (zW (kindOf es) L es) _ _

/-! ## L1, L2 -/

/-- **L1's doom** (after `α`): the batched claim `â + α b̂` is false. -/
def L1Bad (L es : Log) : Prop :=
  69 ≤ es.length ∧ vZ es 0 + alL es * vZ es 1 ≠ aLin M L es + alL es * bLin M L es

/-- L2's initial claim `â + α b̂` (`finLc` (i)). -/
def c0L (es : Log) : F := vZ es 0 + alL es * vZ es 1

/-- L2's tables: per kind `M_α` and the folded column `z̄_j` (`kindTables`). -/
def TL (L es : Log) : Array (Array F) :=
  kindTables (K := 8) (fun j => linM (M.Ak j) (M.Bk j) (rwL es) (alL es))
    (zfoldK (IndF M (kindOf es) _) (rbLc es) (zN (kindOf es) L es (qL (kindOf es))))

/-- **L2's rounds' doom** (`D2` from 69, 14 rounds, degree 2). -/
abbrev D2L : Log → Log → Prop :=
  D2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) (fun _ => 14) (kindExpr 8) (TL M)

/-- **L2's round checks fail** (round 0's is `finLc` (i), the others the rounds' `assertEq`). -/
def RejL2 (L es : Log) : Prop :=
  ∃ l < 14, 69 + 2 * l < es.length ∧ ¬ Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es l

/-! ## L3, L3β -/

/-- L3's eight values. -/
def vL (es : Log) (i : ℕ) : F := readF (msgAt es 97) (16 * i)

/-- **The kind-masked values** (`finLc`'s `packFK`): a node's `0 :: v`, a leaf's `v₀ :: 0^8`. -/
def vM (κ : Kind) (es : Log) (j : Fin 9) : F :=
  if κ.isNode then (if j.val = 0 then 0 else vL es (j.val - 1)) else (if j.val = 0 then vL es 0 else 0)

/-- L2's challenges `r_k`. -/
def rkL (es : Log) : List F := rchs 69 es 14

/-- The per-kind true values `z̄̃_j(r_k)`. -/
def zfL (L es : Log) (j : Fin 9) : F :=
  mle (zfoldK (IndF M (kindOf es) _) (rbLc es) (zN (kindOf es) L es (qL (kindOf es))) j)
    (ptOf 14 (rkL es))

/-- **`finLc` (ii) fails on the log** (from 98; a leaf: the node's (ii) is under ruling 3.16,
R-V-M2): L2's last claim is not `Σ_j v′_j M̃_j(r_k)`. -/
def RejLc2 (L es : Log) : Prop :=
  98 ≤ es.length ∧ (kindOf es).isNode = false ∧ clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 ≠
    ∑ j, vM (kindOf es) es j * mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es))

/-- **L3's doom** (a leaf): some masked value is not the kind's true value. -/
def L3Bad (L es : Log) : Prop :=
  98 ≤ es.length ∧ (kindOf es).isNode = false ∧ ∃ j, vM (kindOf es) es j ≠ zfL M L es j

/-- The batch's true values (a leaf): kind `0`'s, then zeros. The node's batch is under ruling
3.16 (R-V-M1: RS claim 2 has no `W_β` kind factor) and is not stated. -/
def tL (L es : Log) (i : Fin 8) : F := if i.val = 0 then zfL M L es 0 else 0

/-- **The pending Lc claim is false** (a leaf, after `β`): `v_β ≠ Σ_i β^i t_i`. -/
def PendLc (L es : Log) : Prop :=
  99 ≤ es.length ∧ (kindOf es).isNode = false ∧ vBetaL es ≠ ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL M L es i

/-- **The kinds' indicators match the mask**: a node has no `chain` block, a leaf only `chain`
blocks. -/
def ZLM.IndKinds : Prop :=
  ∀ κ t, (κ.isNode = true → M.Ind κ 0 t = 0) ∧ (κ.isNode = false → ∀ j : Fin 9, j ≠ 0 → M.Ind κ j t = 0)

/-! ## Reads -/

section Reads
variable {M} {L es L' es' X : Log} {p : ℕ}

theorem rZ_agree (h : Agree es es' 67) : rZ es = rZ es' := by
  have hk : kindOf es = kindOf es' := kindOf_congr (h.mono (by norm_num))
  unfold rZ rchs; rw [hk]
  refine List.map_congr_left fun j hj => ?_
  have := Kind.m_le (kindOf es'); simp only [List.mem_range, mm] at hj
  exact rch_congr h (by omega)

theorem lin_agree (h : Agree es es' 69) :
    kindOf es = kindOf es' ∧ lamL es = lamL es' ∧ rZ es = rZ es' ∧ alL es = alL es' ∧
      vZ es 0 = vZ es' 0 ∧ vZ es 1 = vZ es' 1 := by
  refine ⟨kindOf_congr (h.mono (by norm_num)), fAt_congr h (by norm_num) 0,
    rZ_agree (h.mono (by norm_num)), fAt_congr h (by norm_num) 0, ?_, ?_⟩ <;>
  simp only [vZ, msgAt_congr h (show 67 < 69 by norm_num)]

theorem aLin_same (h : Same L es L' es' p) (hp : 67 ≤ p) :
    aLin M L es = aLin M L' es' ∧ bLin M L es = bLin M L' es' := by
  have hk : kindOf es = kindOf es' := kindOf_congr (h.1.mono (by omega))
  have hl : lamL es = lamL es' := fAt_congr (h.1.mono hp) (by norm_num) 0
  have hr := rZ_agree (h.1.mono hp)
  have hz : zN (kindOf es) L es = zN (kindOf es) L' es' := by
    funext q b; simp only [zN, zW_same h (by omega)]
  unfold aLin bLin rbLc rwL rhiL
  rw [hz, hk, hl, hr]; exact ⟨rfl, rfl⟩

theorem l1Bad_reads : Reads 69 (L1Bad M) := fun L es L' es' h1 h2 h => by
  obtain ⟨-, -, -, ha, h0, h1'⟩ := lin_agree h.1
  obtain ⟨e1, e2⟩ := aLin_same (M := M) h (by norm_num)
  unfold L1Bad; rw [ha, h0, h1', e1, e2]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem TL_same (h : Same L es L' es' p) (hp : 69 ≤ p) : TL M L es = TL M L' es' := by
  obtain ⟨hk, hl, hr, ha, -, -⟩ := lin_agree (h.1.mono hp)
  have hz : zN (kindOf es) L es = zN (kindOf es) L' es' := by
    funext q b; simp only [zN, zW_same h (by omega)]
  unfold TL rbLc rwL rhiL
  rw [hz, hk, hl, hr, ha]

theorem c0L_agree (h : Agree es es' 69) : c0L es = c0L es' := by
  obtain ⟨-, -, -, ha, h0, h1⟩ := lin_agree h
  unfold c0L; rw [ha, h0, h1]

theorem TL_local : TruthLocal2 69 (fun _ es => c0L es) (TL M) := fun L es es' h =>
  ⟨TL_same (same_of_agree L h) le_rfl, c0L_agree h⟩

theorem TL_size (L es : Log) : ∀ t ∈ TL M L es, t.size = 2 ^ (fun _ => 14) (kindOf es) :=
  kindTables_size _ _

theorem zfL_same (h : Same L es L' es' p) (hp : 97 ≤ p) : zfL M L es = zfL M L' es' := by
  obtain ⟨hk, -, hr, -, -, -⟩ := lin_agree (h.1.mono (by omega))
  have hz : zN (kindOf es) L es = zN (kindOf es) L' es' := by
    funext q b; simp only [zN, zW_same h (by omega)]
  have hk' : rkL es = rkL es' := by
    unfold rkL rchs; exact List.map_congr_left fun j hj => by
      simp only [List.mem_range] at hj; exact rch_congr h.1 (by omega)
  unfold zfL rbLc; rw [hz, hk, hr, hk']

theorem l3Bad_reads : Reads 98 (L3Bad M) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  have hv : ∀ i, vL es i = vL es' i := fun i => by
    simp only [vL, msgAt_congr h.1 (show 97 < 98 by norm_num)]
  have hvm : vM (kindOf es) es = vM (kindOf es') es' := by
    funext j; simp only [vM, hv, hk]
  unfold L3Bad; rw [hvm, zfL_same h (by norm_num), hk]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem pendLc_reads : Reads 99 (PendLc M) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  have hb : vBetaL es = vBetaL es' := by
    simp only [vBetaL, fAt_congr h.1 (show 98 < 99 by norm_num),
      msgAt_congr h.1 (show 97 < 99 by norm_num)]
  have ht : tL M L es = tL M L' es' := by
    funext i; simp only [tL, zfL_same h (by norm_num)]
  unfold PendLc; rw [hb, ht, hk, fAt_congr h.1 (show 98 < 99 by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

/-- L's dooms read the log only through the level-0 word. -/
theorem lDooms_log (h : Same L X L' X p) (hp : 3 ≤ p) :
    (L1Bad M L X ↔ L1Bad M L' X) ∧ (D2L M L X ↔ D2L M L' X) ∧ (L3Bad M L X ↔ L3Bad M L' X) ∧
      (PendLc M L X ↔ PendLc M L' X) := by
  have hz : zN (kindOf X) L X = zN (kindOf X) L' X := by
    funext q b; simp only [zN, zW_same h hp]
  have ha : aLin M L X = aLin M L' X ∧ bLin M L X = bLin M L' X := by
    unfold aLin bLin; rw [hz]; exact ⟨rfl, rfl⟩
  have hf : zfL M L X = zfL M L' X := by unfold zfL; rw [hz]
  refine ⟨by unfold L1Bad; rw [ha.1, ha.2], D2_congrL (by unfold TL; rw [hz]) rfl,
    by unfold L3Bad; rw [hf], by unfold PendLc tL; rw [hf]⟩

end Reads

/-! ## The obligations -/

variable {M}

open Classical in
/-- **L1's squeeze** (§5.2 row L1, `1·2^128`; `batch_count` at 2 claims): from Zend's doom, at most
`2^128` answers `α` make the batched claim true. -/
theorem l1_single (L es : Log) (hl : es.length = 68) :
    (univ.filter fun a => ZendBad M L es ∧ ¬ L1Bad M L (ext1 es a)).card ≤ 1 * 2 ^ 128 := by
  by_cases hz : ZendBad M L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hz h.1)).trans_le (Nat.zero_le _)
  refine batch_count _ (fun i : Fin 2 => if i.val = 0 then vZ es 0 else vZ es 1)
    (fun i : Fin 2 => if i.val = 0 then aLin M L es else bLin M L es) (fun he => ?_)
    fun a ⟨_, hn⟩ => ?_
  · apply hz.2
    have h0 := congrFun he 0; have h1 := congrFun he 1
    simp only [Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false] at h0 h1
    rw [aStar_eq, bStar_eq, h0, h1]
  · have hS := same_ext1 L es a
    rw [hl] at hS
    have hal : alL (ext1 es a) = chF a 0 := by
      have := entAt_ext1 es a; rw [hl] at this
      simp only [alL, fAt, ansAt, this]
    have hv : ∀ j, vZ (ext1 es a) j = vZ es j := fun j => by
      simp only [vZ, msgAt_congr hS.1 (show 67 < 68 by norm_num)]
    obtain ⟨e1, e2⟩ := aLin_same (M := M) hS (by norm_num)
    have hn' : vZ es 0 + chF a 0 * vZ es 1 = aLin M L es + chF a 0 * bLin M L es := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hal, hv, hv, e1, e2]; exact hc⟩
    simpa [Fin.sum_univ_two] using hn'


/-- **Into L2** (`habs` at 69): a false `â + α b̂` is L2's false initial claim
(`lin_trueSum_kinds`). -/
theorem l2_habs {L es : Log} (x : ByteArray × Digest) (hl : es.length = 69) (hb : L1Bad M L es) :
    D2L M L (es ++ [x]) := by
  have hS := same_append L es [x]
  rw [hl] at hS
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 69 (fun _ => 14) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TL_same hS le_rfl, c0L_agree hS.1]
  unfold TL; rw [lin_trueSum_kinds]
  exact hb.2

open Classical in
/-- **L2's squeezes** (§5.2 row L2, `2·2^128`; `D2_single`), with the round checks from `¬ RejL2`. -/
theorem l2_single (L es : Log)
    (hchk : ∀ j, es.length = 69 + 2 * j + 1 → j < 14 →
      Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es j) :
    (univ.filter fun d => D2L M L es ∧ ¬ D2L M L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  D2_single (by norm_num) TL_local (kindExpr_deg 8) card_chF_fiber (TL_size (M := M)) L es hchk

theorem chk_of_not_rejL2 {L es : Log} (hr : ¬ RejL2 L es) (j : ℕ)
    (hj : es.length = 69 + 2 * j + 1) (hjn : j < 14) :
    Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

theorem clR2L_log (L L' X : Log) (l : ℕ) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L X l =
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L' X l := by
  cases l <;> rfl

theorem chkL_agree {L es es' : Log} {l : ℕ} (h : Agree es es' (69 + 2 * l + 1)) :
    Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es l ↔
      Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es' l := by
  have hg : g2At 69 16 readF es l = g2At 69 16 readF es' l := by
    simp only [g2At, msgAt, h (69 + 2 * l) (by omega)]
  have hc := clR2_congr (b := 69) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := fun _ es => c0L es) (L := L) (c0L_agree (h.mono (by omega))) (l := l) (h.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejL2_mono {L es : Log} (x : ByteArray × Digest) (h : RejL2 L es) : RejL2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  exact ⟨j, hj, by simp; omega,
    fun h' => hc ((chkL_agree (agree_append es [x] (by omega))).mp h')⟩

/-- **L2's round checks are a `RejOK`** (the rounds' absorbs are not squeezes). -/
theorem rejL2_ok (habs2 : ∀ j < 14, fsItems[69 + 2 * j]? ≠ some .squeeze) : RejOK RejL2 where
  mono L es x := rejL2_mono x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejL2_mono x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    by_cases he : 69 + 2 * j = es.length
    · exact absurd (he ▸ hit) (habs2 j hj)
    exact ⟨j, hj, by omega, fun h' => hc ((chkL_agree (agree_append es [x] (by omega))).mpr h')⟩
  stab L i hb hci X hX := by
    unfold RejL2 Chk2
    simp only [clR2L_log (L.take i) L X]

/-- **At L3's absorb** (97): a false final L2 claim gives `RejLc2` (`finLc` (ii) fails) or a
wrong masked value (`lin_final_kinds`). -/
theorem l3_habs {L es : Log} (x : ByteArray × Digest) (hl : es.length = 97)
    (hn : (kindOf es).isNode = false) (hd : D2L M L es) :
    RejLc2 M L (es ++ [x]) ∨ L3Bad M L (es ++ [x]) := by
  have hS := same_append L es [x]
  rw [hl] at hS
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  obtain ⟨-, hw⟩ := hd
  have ha : ans3 69 (fun _ => 14) es = 14 := by simp [ans3, hl]
  rw [ha] at hw
  unfold Wrong2 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum (kindExpr 8) (bindAll (TL M L es) (rchs2 69 (fun d => chF d 0) es 14)) 0 =
      ∑ j, mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) * zfL M L es j :=
    lin_final_kinds _ _ _ _ _ _ _ _ (by simp [rchs2])
  rw [hfin] at hw
  obtain ⟨-, hlam, hr, hal, -, -⟩ := lin_agree (hS.1.mono (by norm_num))
  have hrk : rkL (es ++ [x]) = rkL es := by
    unfold rkL rchs; exact List.map_congr_left fun j hj => by
      simp only [List.mem_range] at hj; exact rch_congr hS.1 (by omega)
  have hrw : rwL (es ++ [x]) = rwL es := by unfold rwL rhiL; rw [hlam, hr]
  have hc : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (es ++ [x]) 14 =
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 :=
    clR2_congr (c0L_agree (hS.1.mono (by norm_num))) (hS.1.mono (by norm_num))
  by_cases hrej : RejLc2 M L (es ++ [x])
  · exact .inl hrej
  refine .inr ⟨by simp; omega, ?_⟩
  have hchk : clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 =
      ∑ j, vM (kindOf es) (es ++ [x]) j *
        mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)) := by
    by_contra hne
    exact hrej ⟨by simp; omega, by rw [hk]; exact hn, by rw [hk, hc, hrw, hal, hrk]; exact hne⟩
  refine ⟨by rw [hk]; exact hn, ?_⟩
  rw [zfL_same hS (by norm_num), hk]
  by_contra hall
  push Not at hall
  refine hw (hchk.trans (Finset.sum_congr rfl fun j _ => ?_))
  rw [hall j, mul_comm]

theorem mle_zfoldK_zero {q : ℕ} {Ind : Fin 9 → Fin (2 ^ q) → F} {j : Fin 9} (hI : ∀ t, Ind j t = 0)
    (rb : Fin q → F) (z : Fin (2 ^ (14 + q)) → F) (r : Fin 14 → F) :
    mle (zfoldK Ind rb z j) r = 0 := by
  simp [mle, zfoldK, hI]

open Classical in
/-- **L3β's squeeze** (§5.2 row L3, `7·2^128 ≤ 8·2^128`; `batch_count` at 8 values): from a wrong
masked value, at most `7·2^128` answers `β` make `v_β` equal the true batch. -/
theorem l3b_single (hI : M.IndKinds) (L es : Log) (hl : es.length = 98) :
    (univ.filter fun a => L3Bad M L es ∧ ¬ PendLc M L (ext1 es a)).card ≤ 7 * 2 ^ 128 := by
  by_cases hb : L3Bad M L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hb h.1)).trans_le (Nat.zero_le _)
  have hz : ∀ j : Fin 9, (∀ t, M.Ind (kindOf es) j t = 0) → zfL M L es j = 0 := fun j h =>
    mle_zfoldK_zero (Ind := IndF M (kindOf es) _) (fun t => h t.val) _ _ _
  refine batch_count _ (fun i : Fin 8 => vL es i) (tL M L es) (fun he => ?_) fun a ⟨_, hn⟩ => ?_
  · obtain ⟨-, hn, j, hj⟩ := hb
    by_cases h0 : j = 0
    · subst h0
      have := congrFun he 0
      simp only [tL, vM, hn, Fin.val_zero, if_true] at this hj
      exact hj (by simpa using this)
    · have := hz j fun t => (hI (kindOf es) t).2 hn j h0
      simp only [vM, hn, if_false, show j.val ≠ 0 from fun h => h0 (Fin.ext h)] at hj
      exact hj (by simp [this])
  · have hS := same_ext1 L es a
    rw [hl] at hS
    have hβ : fAt (ext1 es a) 98 0 = chF a 0 := by
      have := entAt_ext1 es a; rw [hl] at this
      simp only [fAt, ansAt, this]
    have hm : msgAt (ext1 es a) 97 = msgAt es 97 := msgAt_congr hS.1 (by norm_num)
    have ht : tL M L (ext1 es a) = tL M L es := by
      funext i; simp only [tL, zfL_same hS (by norm_num)]
    have hn' : vBetaL (ext1 es a) = ∑ i : Fin 8, chF a 0 ^ i.val * tL M L es i := by
      by_contra hc
      exact hn ⟨by rw [length_ext1]; omega, by rw [hS.kind (by norm_num)]; exact hb.2.1,
        by rw [hβ, ht]; exact hc⟩
    rw [← hn', vBetaL, hβ, hm, Finset.sum_range (fun i => chF a 0 ^ i * readF (msgAt es 97) (16 * i))]
    rfl


/-! ## Controls -/

/-- Control: the node's L3 values and batch are not stated (R-V-M1/M2, ruling 3.16). -/
theorem not_pendLc_node {L es : Log} (hn : (kindOf es).isNode = true) : ¬ PendLc M L es :=
  fun h => by rw [h.2.1] at hn; exact Bool.false_ne_true hn

theorem not_l3Bad_node {L es : Log} (hn : (kindOf es).isNode = true) : ¬ L3Bad M L es :=
  fun h => by rw [h.2.1] at hn; exact Bool.false_ne_true hn

/-- Control (the mask): a leaf's values past entry 0, and a node's entry 0, are `0`. -/
theorem vM_leaf {κ : Kind} (hn : κ.isNode = false) (es : Log) {j : Fin 9} (hj : j ≠ 0) :
    vM κ es j = 0 := by
  simp [vM, hn, show j.val ≠ 0 from fun h => hj (Fin.ext h)]

theorem vM_node {κ : Kind} (hn : κ.isNode = true) (es : Log) : vM κ es 0 = 0 := by simp [vM, hn]

/-- Control: the leaf batch has one live value. -/
theorem tL_succ (L es : Log) (i : Fin 7) : tL M L es i.succ = 0 := by simp [tL]

theorem not_l1Bad_short {L es : Log} (h : es.length < 69) : ¬ L1Bad M L es :=
  fun hb => by have := hb.1; omega

/-- Control (positive): `IndKinds` holds for the kind-0-only leaf / no-kind-0 node indicators. -/
theorem indKinds_ex : ZLM.IndKinds ⟨0, 0, fun κ j _ => if κ.isNode = (j ≠ 0) then 1 else 0, 0⟩ := by
  intro κ t
  refine ⟨fun hn => by simp [hn], fun hn j hj => by simp [hn, hj]⟩

/-- Control (negative): the identity-on-kind-0 instance fails it on a node. -/
theorem not_indKinds_id : ¬ (zlmId 0).IndKinds := fun h => by
  have := (h .N30 0).1 rfl
  simp [zlmId] at this

end

end FR.Snd
