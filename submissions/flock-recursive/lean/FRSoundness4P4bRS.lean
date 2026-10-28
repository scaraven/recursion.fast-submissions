-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows E4 end and RS0, §5.2; stage P4b):
-- RS0's column checks at `seq4` (326), E4 end's claim as RS claim 4, the pending claims' doom.
-- The 3.x templates are `FRSoundnessFrRS0`, `FRSoundnessFrRS` (`gL`, `sL`, `DRS0`) and
-- `FRSoundnessFrPend`.
import FRSoundness4P4bE

/-!
# RS0 at revision 4.1 (P4b)

RS0 absorbs at 326 the 128 slices of each claim (`sliceL4`); `finRS` computes `α_j` from them
(`alphaL4`) and the finals bind each `α_j` where it is used (`okRS4`). Here, at the chain's kind
`κ : CKind` (`kindOfC`):

* **`gL4 kf κ es j`**: claim `j`'s weight on level 0's `2^(m − 7)` cells, `eq(p_j, ·)`, times the
  node's **kind factor** for claim 2 (revision 3.16). The kind factor `kf ν β t` (block `t`'s
  `B_β(t) = Σ_i β^i Ind_i(t)`, `β` L3β's challenge at 98) is a parameter: its indicators are the
  revision 4.1 node's block kinds, S-E's (S-G13 F3). A segment's is `1`.
* **`trueL4`** (the same inner weights on the true slices of `f⁽⁰⁾`'s bit planes `rsQ4`),
  **`PendBad4 ok`** (a claim's binding fails at its true value), **`DPend4`** (E4 end's doom: far,
  a false public cell, or `PendBad4`), **`DRS0_4`** (RS0's: far, a false public cell, a false
  slice). Far and the public cells are parameters (`F0`, `Pub`, read before 3): the level-0 word's
  distance is T4's, the node's public cells are S-E's.
* **`habs_RS0_4`**: `DPend4` before RS0's absorb gives `RejRS4` or `DRS0_4` after it
  (`rs_column`); **`rejRS4_log`**; the reads.
* **`trueL4_three`**/**`pendE4_pendBad4`**: on a node, RS claim 4's true value is `ẑ(r′)` at E4's
  `ncR κ` challenges, so E's pending doom (`PendE4`) is `PendBad4` at claim 4.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

theorem CKind.m_le (κ : CKind) : κ.m ≤ 32 := by rcases κ.m_mem with h | h | h <;> omega

theorem CKind.m_ge (κ : CKind) : 30 ≤ κ.m := by rcases κ.m_mem with h | h | h <;> omega

theorem ncR_eq (κ : NodeKind) : ncR κ = (CKind.node κ).m - 7 := rfl

/-! ## Reads of the claim points, weights and slices -/

section Congr
variable {es es' : Log}

theorem rsPtsL4_congr (h : Agree es es' 325) (κ : CKind) : rsPtsL4 κ es = rsPtsL4 κ es' := by
  have hm := CKind.m_le κ
  have hz : zPtL κ.m es = zPtL κ.m es' := by
    unfold zPtL
    exact congrArg ((List.ofFn pinnedRho).drop 1 ++ ·) (List.map_congr_left fun j hj =>
      fAt_congr h (p := 2 + 1 + j / 2) (by simp only [List.mem_range] at hj; omega) (j % 2))
  have hl : lcPtL κ.m es = lcPtL κ.m es' := by
    unfold lcPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 69) (l := 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 15) (l := 8 + l)
        (by simp only [List.mem_range] at hl; omega)]
  have hs : shPtL κ.m es = shPtL κ.m es' := by
    unfold shPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 114) (l := κ.m - 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 114) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  have he : ∀ ν : NodeKind, ePtL4 (ncR ν) es = ePtL4 (ncR ν) es' := fun ν => by
    have := (dims_le' ν).2.2.1
    unfold ePtL4
    rw [List.map_congr_left fun l hl => rch_congr h (b := 275) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  cases κ with
  | seg σ => simp only [rsPtsL4, hz, hl, hs]
  | node ν => simp only [rsPtsL4, hz, hl, hs, he ν]

theorem cwL4_congr (h : Agree es es' 326) (κ : CKind) : cwL4 κ es = cwL4 κ es' := by
  have hm := CKind.m_le κ
  have h1 : xLL es = xLL es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h2 : xSL4 κ es = xSL4 κ es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h0 : fAt es 14 0 = fAt es' 14 0 := fAt_congr h (by norm_num) 0
  unfold cwL4; rw [h0, h1, h2]

theorem sL4_congr (h : Agree es es' 327) (κ : CKind) : sL4 κ es = sL4 κ es' := by
  funext j i
  rw [sL4, sL4, rsPtsL4_congr (h.mono (by norm_num)) κ, sliceL4, sliceL4,
    msgAt_congr h (show 326 < 327 by norm_num)]

theorem alphaL4_congr (h : Agree es es' 327) (κ : CKind) : alphaL4 κ es = alphaL4 κ es' := by
  funext j; simp only [alphaL4, cwL4_congr (h.mono (by norm_num)) κ, sL4_congr h κ]

end Congr

/-! ## The claims' weights and true values -/

/-- **The kind factor at the chain's kind**: a node's `kf ν β t` with L3β's `β` (98); `1` on a
segment. -/
def kfT4 (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (t : ℕ) : F :=
  match κ with
  | .node ν => kf ν (fAt es 98 0) t
  | .seg _ => 1

/-- Claim `j`'s weight on level 0's cube: `eq(p_j, cube u)`, times the kind factor for claim 2;
`0` for a segment's fourth claim. -/
noncomputable def gL4 (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (j : Fin 4)
    (u : Fin (2 ^ (κ.m - 7))) : F :=
  if j.val < (rsPtsL4 κ es).length then
    eqPts ((rsPtsL4 κ es).getD j []) (bitsL ((rsPtsL4 κ es).getD j []).length u) *
      (if j.val = 1 then kfT4 kf κ es (u.val / 2 ^ 7) else 1) else 0

/-- **The bit planes of `f⁽⁰⁾`** (`Q_i(u)` is bit `i` of `f[u]`). -/
noncomputable def rsQ4 (R : FSrc) (L es : Log) (ℓ : ℕ) : Fin 128 → Fin (2 ^ ℓ) → F :=
  fun i u => unpack (R.fz L es u) i

/-- **Claim `j`'s true value**: the inner weights on the true slices `Σ_u g_j(u) Q_i(u)`. -/
noncomputable def trueL4 (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : CKind) (L es : Log)
    (j : Fin 4) : F :=
  ∑ i : Fin 128, cwL4 κ es j i *
    ∑ u, gL4 kf κ es j u * algebraMap F F (rsQ4 R L es (κ.m - 7) i u)

/-- **The RS0 truth** (A.10 RS0): every claim's partials are the true bit-plane claims. -/
def truthRS0_4 (R : FSrc) {J ℓ : ℕ} (L es : Log) (g : Fin J → Fin (2 ^ ℓ) → F)
    (s : Fin J → Fin 128 → F) : Prop :=
  ∀ j i, s j i = ∑ u, g j u * algebraMap F F (rsQ4 R L es ℓ i u)

theorem gL4_congr (kf : NodeKind → F → ℕ → F) {es es' : Log} (h : Agree es es' 325) (κ : CKind) :
    gL4 kf κ es = gL4 kf κ es' := by
  have hk : kfT4 kf κ es = kfT4 kf κ es' := by
    funext t
    cases κ with
    | seg σ => rfl
    | node ν =>
      show kf ν (fAt es 98 0) t = kf ν (fAt es' 98 0) t
      rw [fAt_congr h (show 98 < 325 by norm_num)]
  funext j u; simp only [gL4, rsPtsL4_congr h κ, hk]

theorem rsQ4_same (R : FSrc) {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 3 ≤ p)
    (ℓ : ℕ) : rsQ4 R L es ℓ = rsQ4 R L' es' ℓ := by
  funext i u; simp only [rsQ4, R.fz_same h hp]

theorem trueL4_same (R : FSrc) (kf : NodeKind → F → ℕ → F) {L es L' es' : Log} {p : ℕ}
    (h : R.Sm L es L' es' p) (hp : 326 ≤ p) (κ : CKind) :
    trueL4 R kf κ L es = trueL4 R kf κ L' es' := by
  funext j
  simp only [trueL4, cwL4_congr ((R.agree h).mono hp) κ,
    gL4_congr kf ((R.agree h).mono (by omega)) κ, rsQ4_same R h (by omega)]

/-! ## The pending claims and RS0's doom -/

section Bind
variable (R : FSrc) (kf : NodeKind → F → ℕ → F) (ok : CKind → Log → ℕ → F → Prop)
  (F0 Pub : Log → Log → Prop)

/-- The bindings read the log before RS0's absorb. -/
def OkReads4 : Prop := ∀ κ es es', Agree es es' 326 → ok κ es = ok κ es'

/-- **A pending claim is false**: some claim's binding fails at its true value. -/
def PendBad4 (L es : Log) : Prop :=
  ∃ j : Fin 4, j.val < (rsPtsL4 (kindOfC es) es).length ∧
    ¬ ok (kindOfC es) es j (trueL4 R kf (kindOfC es) L es j)

/-- **The doom before RS0** (E4 end's): far, a public cell false, or a pending claim false. -/
def DPend4 (L es : Log) : Prop := F0 L es ∨ ¬ Pub L es ∨ PendBad4 R kf ok L es

/-- **RS0's doom** at its absorb: far, a public cell false, or a slice false. -/
def DRS0_4 (L es : Log) : Prop :=
  F0 L es ∨ ¬ Pub L es ∨
    ¬ truthRS0_4 R L es (gL4 kf (kindOfC es) es) (sL4 (kindOfC es) es)

end Bind

section BindLemmas
variable {R : FSrc} {kf : NodeKind → F → ℕ → F} {ok : CKind → Log → ℕ → F → Prop}
  {F0 Pub : Log → Log → Prop}

theorem pendBad4_reads (hok : OkReads4 ok) : ReadsS R 326 (PendBad4 R kf ok) :=
  fun L es L' es' h1 h2 h => by
    have hk := kindOfC_congr ((R.agree h).mono (by norm_num))
    simp only [PendBad4, hk, rsPtsL4_congr ((R.agree h).mono (by norm_num)),
      hok _ es es' (R.agree h), trueL4_same R kf h le_rfl]

theorem dPend4_reads (hok : OkReads4 ok) (hF : ReadsS R 3 F0) (hP : ReadsS R 3 Pub) :
    ReadsS R 326 (DPend4 R kf ok F0 Pub) :=
  (hF.mono (by norm_num)).or ((hP.mono (by norm_num)).not.or (pendBad4_reads hok))

theorem rejRS4_log (hok : OkReads4 ok) : RejLog4 (RejRS4 ok) := by
  refine rejLog4_of (q := 327) (by norm_num) (fun _ _ h => h.1) (fun L es L' es' h1 h2 h => ?_)
    (by simpa using (p4b_abs).2.2.2.1)
  have hk := kindOfC_congr (h.mono (by norm_num))
  simp only [RejRS4, hk, rsPtsL4_congr (h.mono (by norm_num)), hok _ es es' (h.mono (by norm_num)),
    alphaL4_congr h]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

/-- **`habs` at RS0's absorb** (A.10 RS0, `rs_column`): if a pending claim is false before the
absorb, then after it a binding fails at the slices' value (`RejRS4`) or a slice is false
(`DRS0_4`). Far words and false public cells carry over. -/
theorem habs_RS0_4 (hok : OkReads4 ok) (hF : ReadsS R 3 F0) (hP : ReadsS R 3 Pub) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = 326) (hd : DPend4 R kf ok F0 Pub L es) :
    RejRS4 ok L (es ++ [x]) ∨ DRS0_4 R kf F0 Pub L (es ++ [x]) := by
  have hag : Agree (es ++ [x]) es 326 := hl ▸ agree_append es [x] le_rfl
  have hS : R.Sm L (es ++ [x]) L es 326 := R.ofAgree L hag
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOfC_congr (hag.mono (by norm_num))
  rcases hd with h | h | ⟨j, hj, hn⟩
  · exact .inr (.inl ((hF.append L es [x] (by omega)).mpr h))
  · exact .inr (.inr (.inl fun h' => h ((hP.append L es [x] (by omega)).mp h')))
  by_cases hr : RejRS4 ok L (es ++ [x])
  · exact .inl hr
  refine .inr (.inr (.inr ?_))
  have hok' : ok (kindOfC es) (es ++ [x]) = ok (kindOfC es) es := hok _ _ _ hag
  have hpts := rsPtsL4_congr (hag.mono (by norm_num)) (kindOfC es)
  have hα : ok (kindOfC es) es j (alphaL4 (kindOfC es) (es ++ [x]) j) := by
    by_contra hc
    exact hr ⟨by simp; omega, j, by rw [hk, hpts]; exact hj, by rw [hk, hok']; exact hc⟩
  have hne : alphaL4 (kindOfC es) (es ++ [x]) j ≠ trueL4 R kf (kindOfC es) L (es ++ [x]) j := by
    rw [trueL4_same R kf hS le_rfl]; intro he; exact hn (he ▸ hα)
  have hcol := rs_column (c := fun i => cwL4 (kindOfC es) (es ++ [x]) j i)
    (s := fun i => sL4 (kindOfC es) (es ++ [x]) j i)
    (t := fun i => ∑ u, gL4 kf (kindOfC es) (es ++ [x]) j u *
      algebraMap F F (rsQ4 R L (es ++ [x]) ((kindOfC es).m - 7) i u)) rfl
    (fun he => hne (by unfold alphaL4 trueL4; exact he.symm))
  rw [hk]
  intro ht
  exact hcol (funext fun i => sub_eq_zero.mpr (ht j i))

end BindLemmas

/-! ## E4 end's claim is RS claim 4 -/

theorem ePtL4_eq (κ : NodeKind) (es : Log) : ePtL4 (ncR κ) es = rPt4 κ es := by
  unfold ePtL4 rPt4 rchs2; exact List.map_congr_left fun _ _ => rfl

/-- **RS claim 4's true value is `ẑ(r′)`** on a node (`pack_unpack`, `eqPts_eq`). -/
theorem trueL4_three (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : NodeKind) (L es : Log) :
    trueL4 R kf (.node κ) L es 3 = mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)) := by
  have hlen : (rsPtsL4 (.node κ) es).length = 4 := rsPtsL4_length _ _
  have hlr : (rPt4 κ es).length = ncR κ := rPt4_length κ es
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have hg : ∀ u : Fin (2 ^ ((CKind.node κ).m - 7)),
      gL4 kf (.node κ) es 3 u = eqPts (rPt4 κ es) (bitsL (ncR κ) u) := by
    intro u
    rw [gL4, h3, ite_pos' (by rw [hlen]; norm_num), ite_neg' (show (3 : ℕ) ≠ 1 by norm_num),
      mul_one]
    simp only [rsPtsL4, List.getD_eq_getElem?_getD]
    rw [show ([zPtL (CKind.node κ).m es, lcPtL (CKind.node κ).m es, shPtL (CKind.node κ).m es] ++
      [ePtL4 (ncR κ) es])[3]? = some (ePtL4 (ncR κ) es) from rfl, Option.getD_some, ePtL4_eq, hlr]
  have hb : ∀ i : Fin 128, bb i = bitBasis i := fun i => by
    simp only [bb, Nat.mod_eq_of_lt i.isLt]
  have hl : trueL4 R kf (.node κ) L es 3 =
      ∑ u ∈ range (2 ^ ncR κ), eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u := by
    unfold trueL4
    rw [← Fin.sum_univ_eq_sum_range (fun u => eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u)]
    simp only [hg, h3, cwL4, cwF, hb, Algebra.algebraMap_self, RingHom.id_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← pack_unpack (R.fz L es u), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rsQ4]; ring
  have hr : mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)) =
      ∑ u ∈ range (2 ^ ncR κ), eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u := by
    rw [mle, ← Fin.sum_univ_eq_sum_range (fun u => eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u)]
    refine sum_congr rfl fun u _ => ?_
    rw [eqPts_eq _ _ hlr (by simp [bitsL]), ptOf_bitsL u.val (ncR κ) u.isLt]
    rfl
  rw [hl, hr]

/-- **E's pending doom is RS0's `PendBad4` at claim 4** (with RS0's bindings `okRS4`). -/
theorem pendE4_pendBad4 {R : FSrc} {kf : NodeKind → F → ℕ → F} {oZ oLc oSh : CKind → Log → F → Prop}
    {L es : Log} (h : PendE4 R L es) : PendBad4 R kf (okRS4 oZ oLc oSh) L es := by
  obtain ⟨κ, hk, -, hne⟩ := h
  refine ⟨3, by rw [hk, rsPtsL4_length]; simp [CKind.isNode], ?_⟩
  rw [hk]
  show ¬ okE4 es (trueL4 R kf (.node κ) L es 3)
  rw [trueL4_three]; exact hne

/-- RS0's bindings read before 326 when Z's, Lc's and Sh's do. -/
theorem okRS4_reads {oZ oLc oSh : CKind → Log → F → Prop}
    (hZ : ∀ κ es es', Agree es es' 326 → oZ κ es = oZ κ es')
    (hL : ∀ κ es es', Agree es es' 326 → oLc κ es = oLc κ es')
    (hSh : ∀ κ es es', Agree es es' 326 → oSh κ es = oSh κ es') : OkReads4 (okRS4 oZ oLc oSh) := by
  intro κ es es' h
  have he : okE4 es = okE4 es' := by
    funext v; simp only [okE4, msgAt_congr h (show 325 < 326 by norm_num)]
  funext j v
  rcases j with _ | _ | _ | j
  · simp only [okRS4, hZ κ es es' h]
  · simp only [okRS4, hL κ es es' h]
  · simp only [okRS4, hSh κ es es' h]
  · simp only [okRS4, he]

/-! ## RS1's count (the core of `hfin` at RS1, 327 … 330) -/

open Classical in
/-- **RS1's count from a false RS0 truth** (A.10 RS1, `rs1_joint`): if some slice claim is wrong,
at most `(7 + J′)·|F|^7` of the draws `(r″, κ)` make the batched switched claim equal its true
value. The frame at `fsRanges4`'s `(326, 4)` is the composition's (T4's `hfin_rs1`). -/
theorem rs1_count4 {J' ℓ : ℕ} {R : FSrc} {L es : Log} {g : Fin (J' + 1) → Fin (2 ^ ℓ) → F}
    {s : Fin (J' + 1) → Fin 128 → F} (h : ¬ truthRS0_4 R L es g s) :
    (univ.filter fun p : (Fin 7 → F) × F =>
      ∑ j, p.2 ^ j.val * rsT s p.1 j = ∑ j, p.2 ^ j.val * rsTruth (rsQ4 R L es ℓ) g p.1 j).card ≤
      (7 + J') * Fintype.card F ^ 7 := by
  refine rs1_joint _ (fun i u => unpack_boolean _ _) g s ?_
  unfold truthRS0_4 at h
  push Not at h
  obtain ⟨j, i, hji⟩ := h
  exact ⟨j, fun hz => hji (sub_eq_zero.mp (congrFun hz i))⟩

/-! ## Controls -/

/-- (+) With the bindings at the true values, no pending claim is false. -/
theorem not_pendBad4_true (R : FSrc) (kf : NodeKind → F → ℕ → F) (L es : Log) :
    ¬ PendBad4 R kf (fun κ _ j v => ∀ hj : j < 4, v = trueL4 R kf κ L es ⟨j, hj⟩) L es := by
  rintro ⟨j, -, hn⟩; exact hn fun _ => rfl

/-- (−) A binding that refuses every value is pending-false, and rejected after RS0. -/
theorem pendBad4_false (R : FSrc) (kf : NodeKind → F → ℕ → F) (L es : Log) :
    PendBad4 R kf (fun _ _ _ _ => False) L es :=
  ⟨0, by rw [rsPtsL4_length]; split_ifs <;> norm_num, not_false⟩

theorem rejRS4_false (L es : Log) (hl : 327 ≤ es.length) : RejRS4 (fun _ _ _ _ => False) L es :=
  ⟨hl, 0, by rw [rsPtsL4_length]; split_ifs <;> norm_num, not_false⟩

/-- (+) With RS0's truth, a claim's slice value is its true value. -/
theorem alphaL4_true {R : FSrc} {kf : NodeKind → F → ℕ → F} {L es : Log} {κ : CKind}
    (h : truthRS0_4 R L es (gL4 kf κ es) (sL4 κ es)) (j : Fin 4) :
    alphaL4 κ es j = trueL4 R kf κ L es j := by
  unfold alphaL4 trueL4; exact sum_congr rfl fun i _ => by rw [h j i]

/-- (−) Zero slices give every claim the value `0`. -/
theorem alphaL4_zero {κ : CKind} {es : Log} (h : ∀ j i, sliceL4 es j i = 0) (j : Fin 4) :
    alphaL4 κ es j = 0 := by
  unfold alphaL4 sL4; exact sum_eq_zero fun i _ => by split_ifs <;> simp [h]

/-- (+) A segment's kind factor is `1` (it has no node kinds). -/
theorem kfT4_seg (kf : NodeKind → F → ℕ → F) (σ : SegKind) (es : Log) (t : ℕ) :
    kfT4 kf (.seg σ) es t = 1 := rfl

end FR.Snd.P4b
