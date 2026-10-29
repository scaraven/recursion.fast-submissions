-- New for `flock-recursive` (BLUEPRINT A.9 `finPf`'s `w0V`, revision 3.16; stage S-G11).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrRnd
import FRSoundnessFrLN
import FRSoundnessCoreRows

/-!
# `hW0`: the verifier's `Ŵ₀(P₀)` is the front's `wHatL W₀L … 0`

* **Spec side** (no run): **`wHat0_spec`** — `wHatL W₀L L es 0` is `rsWeightS` at the log's claim
  points (`rsPtsL`), `r″`, `κ`, L3β's `β` (a node; `1` on a leaf), plus a node's public cells
  (`cellsVal`). Claim 2's weight is the kind-weighted one: `termK` (`rsWeight_kind_eq` at `Φ = id`,
  `kindFac_frob`, `kwSL_eq`); a leaf's is the plain one (`kwSL_one`, `kwS_one`).
* **Run side**: the registers `w0V` reads hold those values (`chalsF_view`, `coordsR_view`,
  `oneR_view`, `p1_facts`, `tail_vals`); **`w0V_run`** (`hW0`'s form).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

/-! ## The spec side -/

/-- The node kinds' indicators in K (`KW.kwS`'s). -/
def indK (i : Fin 8) (t : Fin (2 ^ 16)) : K := selOf (KW.ivsQ 16 (KW.nodeKinds.getD i .free)) t

/-- The kind factor in K. -/
theorem iota_kindFac (β : F) (t : Fin (2 ^ 16)) :
    algebraMap F K (kindFac indKW β t) = kindFac indK (algebraMap F K β) t := by
  simp only [kindFac, indKW, indK, selOf, map_sum, map_mul, map_pow, map_list_sum, List.map_map,
    Function.comp_def, apply_ite (algebraMap F K), map_one, map_zero]

theorem indK_bit (i : Fin 8) (t : Fin (2 ^ 16)) : indK i t = 0 ∨ indK i t = 1 := by
  have h := indKW_eq i t.isLt
  have e : indK i t = algebraMap F K (indKW i t) := by
    simp only [indK, indKW, selOf, map_list_sum, List.map_map, Function.comp_def,
      apply_ite (algebraMap F K), map_one, map_zero]
  rw [e, h]; split_ifs <;> simp

/-- The extension of `eq(q, ·)·B_γ(block)` over `7 + 16` coordinates (`rsWeight_kind_eq` at
`Φ = id`). -/
theorem mle_kind0 (q ρ : List K) (γ : K) :
    mle (fun y : Fin (2 ^ 23) => eq (ptOf 23 q) (cube y) *
        kindFac indK γ ⟨y.val / 2 ^ 7 % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩) (ptOf 23 ρ) =
      ∑ κ : Fin 8, γ ^ κ.val * eq (ptOf 7 q) (ptOf 7 ρ) *
        ∑ t, indK κ t * eq (ptOf 16 (q.drop 7)) (cube t) * eq (ptOf 16 (ρ.drop 7)) (cube t) := by
  have h := rsWeight_kind_eq (R := K) (a := 7) (b := 16) [] indK indK_bit γ (ptOf 7 q)
    (ptOf 7 ρ) (ptOf 16 (q.drop 7)) (ptOf 16 (ρ.drop 7))
  rw [← ptOfK_split, ← ptOfK_split] at h
  simp only [List.length_nil, pow_zero, range_one, sum_singleton, mul_one, pow_one] at h
  have hP : ∀ x : K, Phi ([] : List K) x = x := fun x => rfl
  have h0 : (phiTable ([] : List K)).getD 0 0 = 1 := rfl
  have hI : ∀ y : Fin (2 ^ (7 + 16)),
      hiIdx y = ⟨y.val / 2 ^ 7 % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩ := fun y => by
    apply Fin.ext; simp only [hiIdx]; have := y.isLt; omega
  simp only [hP, h0, one_mul, hI] at h
  exact h

theorem kwSL_eq (γ : K) (q ρ : List K) (hq : q.length = 23) (hρ : ρ.length = 23) :
    kwSL γ q ρ = ∑ κ : Fin 8, γ ^ κ.val * eq (ptOf 7 q) (ptOf 7 ρ) *
      ∑ t, indK κ t * eq (ptOf 16 (q.drop 7)) (cube t) * eq (ptOf 16 (ρ.drop 7)) (cube t) := by
  have ht : ∀ r : List K, r.length = 23 → ptOf 7 (r.take 7) = ptOf 7 r := fun r hr => by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_take, l.isLt, if_true]
  unfold kwSL KW.kwS
  rw [hρ, show 23 - 7 = 16 from rfl, eqPts_eq (ℓ := 7) _ _ (by simp [hq]) (by simp [hρ]),
    ht q hq, ht ρ hρ, mul_sum, Finset.sum_range]
  exact sum_congr rfl fun κ _ => by simp only [indK]; ring

/-- **Claim 2's weight on a node** (the kind factor), in `rsWeightS`'s form (`kwSL`). -/
theorem termK (fs : List F) {p : List F} (hp : p.length = 23) (es : Log) (ρ : List K)
    (hρ : ρ.length = 23) :
    mle (fun y : Fin (2 ^ 23) => algebraMap F K
        (Phi fs (eqPts p (bitsL 23 y) * kfT .N30 es (y.val / 2 ^ 7)))) (ptOf 23 ρ) =
      ∑ k ∈ range (2 ^ fs.length), K.ofF ((phiTable fs).getD k 0) *
        kwSL (sqIter k (K.ofF (fAt es 98 0))) ((p.map (algebraMap F K)).map (sqIter k)) ρ := by
  simp only [iota_Phi, map_mul, iota_eqPts_bits hp, kfT, Kind.isNode, ↓reduceIte, iota_kindFac]
  rw [mle_sum]
  refine sum_congr rfl fun k _ => congrArg _ ?_
  simp only [mul_pow, eq_frob, kindFac_frob indK indK_bit, ptOf_sq]
  have hk : ∀ t, ∑ κ : Fin 8, algebraMap F K (fAt es 98 0) ^ (κ.val * 2 ^ k) * indK κ t =
      kindFac indK (sqIter k (K.ofF (fAt es 98 0))) t := fun t => by
    simp only [kindFac, sqIter_eq, ← pow_mul, mul_comm (2 ^ k)]; rfl
  simp only [hk]
  rw [mle_kind0, kwSL_eq _ _ _ (by simp [hp]) hρ]

theorem rsRL_length (es : Log) : (rsRL es).length = 7 := by simp [rsRL]

/-- Claim `p`'s weight term (index `i`): plain, or claim 2's with the kind factor. -/
theorem termW (κ : Kind) (es : Log) (ρ : List K) (hρ : ρ.length = nrP 0 κ) (p : List F)
    (hp : p.length = nrP 0 κ) (i : ℕ) :
    mle (fun y : Fin (2 ^ nrP 0 κ) => algebraMap F K (Phi (rsRL es)
        (eqPts p (bitsL (nrP 0 κ) y) * if i = 1 then kfT κ es (y.val / 2 ^ 7) else 1)))
        (ptOf _ ρ) =
      ∑ k ∈ range 128, K.ofF ((phiTable (rsRL es)).getD k 0) *
        (if i = 1 then kwSL (sqIter k (K.ofF (if κ.isNode then fAt es 98 0 else 1)))
          ((p.map (algebraMap F K)).map (sqIter k)) ρ
        else eqPts ((p.map (algebraMap F K)).map (sqIter k)) ρ) := by
  have h128 : (128 : ℕ) = 2 ^ (rsRL es).length := by rw [rsRL_length]; rfl
  by_cases hi : i = 1
  · simp only [hi, ↓reduceIte]
    by_cases hn : κ.isNode = true
    · obtain rfl := kind_node hn
      rw [h128]
      exact termK _ hp es ρ hρ
    · have hk : ∀ t, kfT κ es t = 1 := fun t => by simp [kfT, hn]
      simp only [hk, mul_one, hn, Bool.false_eq_true, ↓reduceIte, sqIter_eq]
      rw [termP _ hp ρ hρ, ← h128]
      refine sum_congr rfl fun k _ => ?_
      rw [show K.ofF 1 = 1 from map_one (algebraMap F K), one_pow, kwSL_one _ _ (by simp [hp, hρ])]
      rw [hρ]; cases κ <;> decide
  · simp only [hi, ↓reduceIte, mul_one]
    rw [termP _ hp ρ hρ, ← h128]

theorem mle_zipIdx (κ : Kind) (es : Log) (ρ : List K) (hρ : ρ.length = nrP 0 κ) :
    ∀ (ps : List (List F)) (i₀ : ℕ), (∀ p ∈ ps, p.length = nrP 0 κ) →
    mle (fun y : Fin (2 ^ nrP 0 κ) => algebraMap F K (((ps.zipIdx i₀).map fun p =>
        rsKL es ^ p.2 * Phi (rsRL es) (eqPts p.1 (bitsL p.1.length y) *
          if p.2 = 1 then kfT κ es (y.val / 2 ^ 7) else 1)).sum)) (ptOf _ ρ) =
      ((ps.zipIdx i₀).map fun p => K.ofF (rsKL es) ^ p.2 * ∑ k ∈ range 128,
        K.ofF ((phiTable (rsRL es)).getD k 0) *
          (if p.2 = 1 then kwSL (sqIter k (K.ofF (if κ.isNode then fAt es 98 0 else 1)))
            ((p.1.map (algebraMap F K)).map (sqIter k)) ρ
          else eqPts ((p.1.map (algebraMap F K)).map (sqIter k)) ρ)).sum
  | [], _, _ => by simp [mle]
  | p :: ps, i₀, h => by
    have hp := h p List.mem_cons_self
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, map_add, mle_add', map_mul,
      map_pow, mle_smul, hp]
    rw [mle_zipIdx κ es ρ hρ ps (i₀ + 1) fun q hq => h q (List.mem_cons_of_mem _ hq),
      termW κ es ρ hρ p hp i₀]
    rfl

theorem rsPtsL_len (κ : Kind) (es : Log) : ∀ p ∈ rsPtsL κ es, p.length = nrP 0 κ := by
  intro p hp
  rw [nrP_zero]
  cases κ <;> simp only [rsPtsL, Kind.isNode, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl <;> simp [zPtL, lcPtL, shPtL, ePtL, Kind.m]

/-- **The RS weight's extension is `rsWeightS`** at the log's claim points, `r″`, `κ` and
(node) L3β's `β`. -/
theorem mleW_spec (κ : Kind) (es : Log) (ρ : List K) (hρ : ρ.length = nrP 0 κ) :
    mleN (nrP 0 κ) (fun y => algebraMap F K (wrsL κ es y)) (ptOf _ ρ) =
      rsWeightS (rsRL es).toArray ((rsPtsL κ es).map fun p => (p.map (algebraMap F K)).toArray)
        (rsKL es) (if κ.isNode then fAt es 98 0 else 1) ρ.toArray := by
  unfold mleN wrsL rsWeightS
  rw [mle_zipIdx κ es ρ hρ _ 0 (rsPtsL_len κ es), List.zipIdx_map, List.map_map]
  rfl

/-- **The front's `Ŵ₀(P₀)`** (`wHatL W₀L … 0`) is `w0V`'s value at the log's values: `rsWeightS`
and, for a node, the public cells' sum (`cellsVal`). -/
theorem wHat0_spec (L es : Log) (ρ : List K) (hρ : ρ.length = nrP 0 (kindOf es))
    (hρv : ∀ v < nrP 0 (kindOf es), ρ.getD v 0 = ptL es 0 v) :
    wHatL W₀L L es 0 =
      rsWeightS (rsRL es).toArray
          ((rsPtsL (kindOf es) es).map fun p => (p.map (algebraMap F K)).toArray)
          (rsKL es) (if (kindOf es).isNode then fAt es 98 0 else 1) ρ.toArray +
        (if (kindOf es).isNode then cellsVal ρ.toArray (kpL es) pfCells (kpL es * kpL es) 0
         else 0) := by
  have hpt : (fun v : Fin (nrP 0 (kindOf es)) => ptL es 0 v) = ptOf _ ρ := by
    funext v; exact (hρv v v.isLt).symm
  rw [wHatL, mleP, hpt]
  unfold W₀L
  rw [mleN_w0F _ _ _ cells_lt, mleW_spec _ _ ρ hρ]
  congr 1
  cases hk : kindOf es
  all_goals simp only [cellsOf, Kind.isNode, Bool.false_eq_true, ↓reduceIte, List.length_nil,
    range_zero, sum_empty]
  rw [cellsVal_eq, zero_add, ← pfCells_eq]
  simp only [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [K.smulF_eq_mul, ← K.algebraMap_eq_ofF, eqCellK_eq, show kpL es ^ (x + 2) =
    kpL es * kpL es * kpL es ^ x by ring]
  congr 2
  funext v
  simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## The run side -/

theorem map_window {α : Type} {l : List ℕ} {K : ℕ} {f g : ℕ → α} (hK : l.length = K)
    (hg : ∀ j < K, f (l.getD j 0) = g j) (d t : ℕ) :
    ((l.drop d).take t).map f = (List.range (min t (K - d))).map (fun i => g (d + i)) := by
  apply List.ext_getElem (by simp [hK])
  intro i h1 h2
  simp only [List.length_map, List.length_take, List.length_drop, hK] at h1
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
  rw [← hg (d + i) (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem map_window' {α : Type} {l : List ℕ} {K : ℕ} {f g : ℕ → α} (hK : l.length = K)
    (hg : ∀ j < K, f (l.getD j 0) = g j) (d t : ℕ) :
    ((l.take t).drop d).map f = (List.range (min t K - d)).map (fun i => g (d + i)) := by
  apply List.ext_getElem (by simp [hK])
  intro i h1 h2
  simp only [List.length_map, List.length_take, List.length_drop, hK] at h1
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
  rw [← hg (d + i) (by omega), List.getD_eq_getElem _ _ (by omega)]

section Run
variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem chals_len {n : ℕ} (hn : n < phases.length) {f K deg : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f K deg false real) {fi : FinIn}
    (hfi : fi.outs = skeleton.2.outs) {name : String} (hix : phaseIx name = n) :
    (chals fi name K).length = K := by
  obtain ⟨cl, last, hout⟩ := genPhase_roundsF (n := n) (cAt n) hsh
  rw [chals, outsOf, hfi, hix, skeleton_outs hn, hout]; simp

theorem coordsR_len (h : SkRun impl κ inp tr y) {n k : ℕ} {nf : Kind → ℕ}
    (hn : n < phases.length) (hsh : phases[n].shape = .squeezes k (.coords nf)) (hk : 0 < k)
    {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) {name : String} (hix : phaseIx name = n) :
    (coordsR fi name).length = 2 * k := by
  obtain ⟨b, hout, -, -⟩ := coords_view h hn hsh hk
  rw [coordsR, outsOf, hfi, hix, hout]; simp

theorem srcVal_f {r : Array Val} {x : ℕ} {v : F} (h : rd r x = .f v) :
    srcVal r (.f x) = algebraMap F K v := by
  rw [srcVal, h]; exact K.smulF_one v

variable (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

theorem chalsV (n : ℕ) (hn : n < phases.length) {f Kr deg : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f Kr deg false real) (hf : f ≤ nFields) (hn0 : 0 < n)
    {name : String} (hix : phaseIx name = n) :
    ∀ j < Kr, (fun x => srcVal R (.f x)) ((chals fi name Kr).getD j 0) =
      algebraMap F K (rch (phStart n) (fsOf tr items) j) := fun _ hj =>
  srcVal_f (chalsF_view h hn hsh hf hn0 hfi hix hR hj).2

theorem zSrc_val {m : ℕ} (hm : m ≤ 32) :
    (zSrc fi m).map (srcVal R) = (zPtL m (fsOf tr items)).map (algebraMap F K) := by
  have hl := coordsR_len h (n := 3) (by rw [phases_length]; omega) rfl (by norm_num) hfi
    phaseIx_vals.1
  have hg : ∀ j < 2 * 10, (fun x => srcVal R (.f x)) ((coordsR fi "Z1").getD j 0) =
      algebraMap F K (coordAt (fsOf tr items) 2 j) := fun j hj =>
    srcVal_f (coordsR_view h (n := 3) (by rw [phases_length]; omega) rfl (by norm_num) hfi
      phaseIx_vals.1 hR hj).2
  have hw := map_window (f := fun x => srcVal R (.f x))
    (g := fun j => algebraMap F K (coordAt (fsOf tr items) 2 j)) hl hg 0 (m - 13)
  simp only [List.drop_zero, zero_add] at hw
  rw [zSrc, zPtL, List.map_append, List.map_append, List.map_map, List.map_map, List.map_map]
  rw [show (fun x => srcVal R (.f x)) = srcVal R ∘ PtSrc.f from rfl] at hw
  rw [hw, show min (m - 13) (2 * 10) = m - 13 by omega]
  rfl

theorem chalsW (n b : ℕ) (hn : n < phases.length) {f Kr deg : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f Kr deg false real) (hf : f ≤ nFields) (hn0 : 0 < n)
    {name : String} (hix : phaseIx name = n) (hb : phStart n = b) (d t : ℕ) :
    (((chals fi name Kr).drop d).take t).map (srcVal R ∘ PtSrc.f) =
      (List.range (min t (Kr - d))).map (fun i => algebraMap F K (rch b (fsOf tr items) (d + i))) := by
  rw [← hb]
  exact map_window (f := fun x => srcVal R (.f x)) (chals_len hn hsh hfi hix)
    (chalsV h hfi hR n hn hsh hf hn0 hix) d t

theorem chalsW' (n b : ℕ) (hn : n < phases.length) {f Kr deg : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f Kr deg false real) (hf : f ≤ nFields) (hn0 : 0 < n)
    {name : String} (hix : phaseIx name = n) (hb : phStart n = b) (d t : ℕ) :
    (((chals fi name Kr).take t).drop d).map (srcVal R ∘ PtSrc.f) =
      (List.range (min t Kr - d)).map (fun i => algebraMap F K (rch b (fsOf tr items) (d + i))) := by
  rw [← hb]
  exact map_window' (f := fun x => srcVal R (.f x)) (chals_len hn hsh hfi hix)
    (chalsV h hfi hR n hn hsh hf hn0 hix) d t

theorem lcSrc_val {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (lcSrc fi m).map (srcVal R) = (lcPtL m (fsOf tr items)).map (algebraMap F K) := by
  have hL := chalsW h hfi hR 8 69 (by rw [phases_length]; omega) rfl (by decide) (by norm_num)
    phaseIx_vals.2.2.2.2.1 frW0_starts.2.2.1 7 7
  have hZ := chalsW' h hfi hR 5 15 (by rw [phases_length]; omega) rfl (by decide) (by norm_num)
    phaseIx_vals.2.2.1 frW0_starts.2.1 8 (m - 6)
  have hl7 : ((chals fi "L2" 14).drop 7).take 7 = (chals fi "L2" 14).drop 7 :=
    List.take_of_length_le (by
      rw [List.length_drop, chals_len (n := 8) (by rw [phases_length]; omega) rfl hfi
        phaseIx_vals.2.2.2.2.1])
  rw [hl7] at hL
  rw [lcSrc, lcPtL, List.map_append, List.map_append, List.map_map, List.map_map, List.map_map,
    List.map_map, hL, hZ, show min (m - 6) 26 - 8 = m - 14 by omega]
  rfl

theorem shSrc_val {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (shSrc fi m).map (srcVal R) = (shPtL m (fsOf tr items)).map (algebraMap F K) := by
  have h1 := chalsW h hfi hR 12 114 (by rw [phases_length]; omega) rfl (by decide) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.1 frW0_starts.2.2.2.1 (m - 7) 3
  have h2 := chalsW h hfi hR 12 114 (by rw [phases_length]; omega) rfl (by decide) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.1 frW0_starts.2.2.2.1 0 (m - 14)
  rw [List.drop_zero] at h2
  rw [shSrc, shPtL, List.map_append, List.map_append, List.map_append, List.map_append,
    List.map_map, List.map_map, List.map_map, List.map_map, h1, h2,
    show min 3 (28 - (m - 7)) = 3 by omega, show min (m - 14) (28 - 0) = m - 14 by omega]
  simp [srcVal, Function.comp_def]

theorem eSrc_val :
    (eSrc fi).map (srcVal R) = (ePtL (fsOf tr items)).map (algebraMap F K) := by
  have h1 := chalsW h hfi hR 21 265 (by rw [phases_length]; omega) rfl (by decide) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 frW0_starts.2.2.2.2.1 0 23
  rw [List.drop_zero, List.take_of_length_le (by rw [chals_len (n := 21)
    (by rw [phases_length]; omega) rfl hfi phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])] at h1
  rw [eSrc, ePtL, List.map_map, List.map_map, h1]
  simp [Function.comp_def]

/-- **The claim points `rsWeight` gets are the log's** (`pfPts`, `rsPtIx`). -/
theorem rsPtsV_eq :
    rsPtsV κ' fi R = (rsPtsL κ' (fsOf tr items)).map fun p => (p.map (algebraMap F K)).toArray := by
  have hz := zSrc_val h hfi hR (m := κ'.m) (Kind.m_le κ')
  have hl := lcSrc_val h hfi hR (m := κ'.m) (by cases κ' <;> decide) (Kind.m_le κ')
  have hs := shSrc_val h hfi hR (m := κ'.m) (by cases κ' <;> decide) (Kind.m_le κ')
  have he := eSrc_val h hfi hR
  cases κ' <;> simp only [Kind.m] at hz hl hs <;>
    simp [rsPtsV, rsPtsL, rsPtIx, pfPts, ptV, Kind.isNode, Kind.m, hz, hl, hs, he]

/-- **`P₀`'s registers hold `ptL es 0`** (`p1_facts` at level 0, `tail_vals` at `k = 1`). -/
theorem p0_vals :
    ((p0Regs fi κ.m).map fun x => (rd R x).toK).length = nrP 0 κ ∧
      ∀ v < nrP 0 κ, ((p0Regs fi κ.m).map fun x => (rd R x).toK).getD v 0 =
        ptL (fsOf tr items) 0 v := by
  obtain ⟨b, hs, -, hv, -, -, hlt, -⟩ := p1_facts h hfi (i := 0) (by norm_num)
  have ht := (tail_vals h hfi hR (k := 1) le_rfl (by norm_num)).1
  have hA : (sRegs fi 0).map (fun x => (rd R x).toK) =
      (List.range (hEll 0)).map (sAt (fsOf tr items) 0) := by
    have hmem : ∀ x ∈ sRegs fi 0, x < (#[] ++ y.1.toArray).size := fun x hx =>
      hlt x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    rw [hs, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    have hx : b + 13 * j + 6 < (#[] ++ y.1.toArray).size :=
      hmem _ (by rw [hs]; exact List.mem_map.mpr ⟨j, hj, rfl⟩)
    simp only [Function.comp, hR.rd hx, hv j hj']
    rfl
  have hn : nrP 0 κ = hEll 0 + mLog κ 0 := by rw [nrP, lvl_ell κ (by norm_num)]
  rw [p0Regs, List.map_append, hA, ht]
  refine ⟨by simp [hn], fun v hv' => ?_⟩
  rw [ptL_lt (k := 0) (by norm_num)]
  dsimp only
  by_cases h0 : v < hEll 0
  · rw [List.getD_append _ _ _ _ (by simpa using h0), if_pos h0,
      List.getD_eq_getElem _ _ (by simpa using h0)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simpa using h0), if_neg h0]
    simp only [List.length_map, List.length_range]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, zero_add]

end Run

theorem phStart_10 : phStart 10 = 98 := by simp only [phStart, fsStarts_eq]; decide

/-- **`hW0`** (`kstate_front_ofR`'s form): on an accepted run of `gen (sfFinals finP finPf)` with
`rsWeight` at its spec (`implC_meets`), `w0V` on any file extending the skeleton's is the front's
`wHatL W₀L L es 0` (`wHat0_spec` at the run's registers). -/
theorem w0V_run {impl : OpImpl}
    (hrs : ∀ r ps k β p, r.size = 7 → 23 ≤ p.size → impl.rsWeight r ps k β p = rsWeightS r ps k β p)
    (vk : Digest) :
    ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V impl k fi r' = wHatL W₀L L (fsOf tr items) 0 := by
  intro k c π L tr y _ _ hk hsem _ hy fi r' hfi hR
  obtain ⟨y', hy', hfl, -⟩ := accept_chain impl k ⟨vk, c, π⟩ _ noAsk_sf hsem
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  obtain ⟨hl, hq⟩ := fsQ_gen ⟨vk, c, π⟩ impl _ _ hsem
  have hS : SkRun impl k ⟨vk, c, π⟩ tr y' := ⟨hy', hfl, hl, hq⟩
  have hkind : kindOf (fsOf tr items) = k := kindOf_fsQ hq hk
  obtain ⟨hρ, hρv⟩ := p0_vals hS hfi hR
  rw [wHat0_spec L _ _ (by rw [hkind]; exact hρ) (by rw [hkind]; exact hρv), hkind]
  have hpt : ptF r' ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0) =
      (rsRL (fsOf tr items)).toArray := by
    simp only [ptF, rsRL, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun p hp =>
      (rs1_val hS hfi hR (by simp at hp; omega)).2)
  have hκ := (rs1_val hS hfi hR (show 7 < 8 by norm_num)).2
  have hβ : fv r' ((outsOf fi "L3β").headD 0) = fAt (fsOf tr items) 98 0 := by
    rw [fv, (oneR_view hS (n := 10) (by rw [phases_length]; omega) rfl hfi
      phaseIx_vals.2.2.2.2.2.1 hR).2, phStart_10]; rfl
  have hkp : fv r' ((outsOf fi "B'").headD 0) = kpL (fsOf tr items) := by
    rw [fv, (oneR_view hS (n := 25) (by rw [phases_length]; omega) rfl hfi
      phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hR).2, frW0_starts.2.2.2.2.2.2.2.1]; rfl
  have hp0 : p0V k fi r' = ((p0Regs fi k.m).map fun x => (rd r' x).toK).toArray := rfl
  unfold w0V
  rw [hpt, hκ, hrs _ _ _ _ _ (by simp [rsRL]) (by rw [hp0, List.size_toArray, hρ]; cases k <;> decide),
    rsPtsV_eq hS hfi hR, hp0, hkp]
  simp only [hβ]
  rfl

/-! ## Controls -/

/-- Control (positive): on a leaf, claim 2's weight is the plain one (`β = 1`). -/
theorem kwSL_leaf (q ρ : List K) (hq : q.length = 25) (hρ : ρ.length = 25) :
    kwSL 1 q ρ = eqPts q ρ := kwSL_one q ρ (by rw [hq, hρ]) (by rw [hρ]; norm_num)

end FR.Snd
