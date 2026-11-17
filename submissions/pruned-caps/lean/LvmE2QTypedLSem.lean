-- New for lvm2 MB-LIN (MBL-C2, 2026-11-16): the soundness of `mbLinG` (MBL-STMT 7c): the gadget's three claims are
-- V_S's `mbClaimsN` on the native bus decomposition at the mini-bus GKR's outputs.
import LvmE2QTypedL
import LvmS2GLLin
import LvmQTypedHarS

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped

/-! ## Lists and sums -/

theorem f2_getD {α β : Type} {P : β → α → Prop} : ∀ {l : List β} {r : List α}, List.Forall₂ P l r →
    ∀ (z : α) (i : Nat) (hi : i < l.length), P l[i] (r.getD i z)
  | _, _, .nil, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, _, .cons h _, _, 0, _ => h
  | _, _, .cons _ t, z, i + 1, hi => by
    simp only [List.getD_cons_succ, List.getElem_cons_succ]
    exact f2_getD t z i (by simpa using hi)

theorem sum_filter_add {α : Type} (p : α → Bool) (G : α → FE) (l : List α) :
    ((l.filter p).map G).sum + ((l.filter fun a => !p a).map G).sum = (l.map G).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a
    · simp only [List.filter_cons, h, Bool.not_false, if_true, List.map_cons, List.sum_cons, ← ih]
      simp; ring
    · simp only [List.filter_cons, h, Bool.not_true, if_true, List.map_cons, List.sum_cons, ← ih]
      simp; ring

theorem sum_ite_nodup {κ : Type} [BEq κ] [LawfulBEq κ] (v : FE) (x : κ) : ∀ K : List κ, K.Nodup → x ∈ K →
    (K.map fun k => if (x == k) = true then v else 0).sum = v
  | [], _, h => absurd h List.not_mem_nil
  | k :: K, hn, hx => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons]
    by_cases hk : x = k
    · subst hk
      have : (K.map fun k => if (x == k) = true then v else 0).sum = 0 :=
        List.sum_eq_zero fun y hy => by
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hy
          exact if_neg fun h => hn.1 (by rw [beq_iff_eq] at h; exact h ▸ hk')
      rw [this, if_pos (beq_self_eq_true x), add_zero]
    · rw [if_neg (fun h => hk (beq_iff_eq.mp h)), sum_ite_nodup v x K hn.2 ((List.mem_cons.mp hx).resolve_left hk),
        zero_add]

/-- **Regrouping**: summing each key's members over a duplicate-free list of keys that holds every key. -/
theorem sum_group {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (G : α → FE) (K : List κ) (hK : K.Nodup) :
    ∀ l : List α, (∀ a ∈ l, key a ∈ K) →
      (K.map fun k => ((l.filter fun a => key a == k).map G).sum).sum = (l.map G).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_group key G K hK l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have e : ∀ k, (((a :: l).filter fun b => key b == k).map G).sum =
        (if (key a == k) = true then G a else 0) + ((l.filter fun b => key b == k).map G).sum := by
      intro k; by_cases hk : (key a == k) = true <;> simp [List.filter_cons, hk]
    simp only [e]
    rw [List.sum_map_add, sum_ite_nodup _ _ K hK (h a List.mem_cons_self), ih, List.map_cons, List.sum_cons]

theorem nodup_eraseDups' {κ : Type} [BEq κ] [LawfulBEq κ] :
    ∀ (n : Nat) (l : List κ), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => List.nodup_nil
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_eraseDups' n _ (le_trans (List.length_filter_le _ _) (by simpa using h))⟩
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm

theorem nodup_eraseDups {κ : Type} [BEq κ] [LawfulBEq κ] (l : List κ) : l.eraseDups.Nodup :=
  nodup_eraseDups' l.length l le_rfl

/-- Regrouping by `eraseDups` of the keys (the plan's classes). -/
theorem sum_group_eraseDups {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (G : α → FE) (l : List α) :
    (((l.map key).eraseDups).map fun k => ((l.filter fun a => key a == k).map G).sum).sum = (l.map G).sum :=
  sum_group key G _ (nodup_eraseDups _) l fun a ha => List.mem_eraseDups.mpr (List.mem_map_of_mem ha)

theorem sum_filterMap {α β : Type} (f : α → Option β) (F : β → FE) (l : List α) :
    ((l.filterMap f).map F).sum = (l.map fun a => ((f a).map F).getD 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : f a <;> simp [List.filterMap_cons, h, ih]

theorem sum_flatMap' {α β : Type} (f : α → List β) (F : β → FE) (l : List α) :
    ((l.flatMap f).map F).sum = (l.map fun a => ((f a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_zipIdx_filter {α : Type} (l : List α) (p : α → Bool) (G : α × Nat → FE) (F : α → FE)
    (hG : ∀ x ∈ l.zipIdx, p x.1 = true → G x = F x.1) :
    ((l.zipIdx.filter fun x => p x.1).map G).sum = ((l.filter p).map F).sum := by
  rw [List.map_congr_left fun x hx => hG x (List.mem_of_mem_filter hx) (List.mem_filter.mp hx).2]
  rw [show (fun x : α × Nat => F x.1) = F ∘ Prod.fst from rfl, ← List.map_map]
  congr 2
  rw [show (fun x : α × Nat => p x.1) = p ∘ Prod.fst from rfl, ← List.filter_map, List.zipIdx_map_fst]

/-! ## Linear functionals on forms -/

/-- `Σ coefficient · h(monomial)`. -/
def lfE (h : List Nat → FE) (f : Lvm.Form) : FE := (f.terms.map fun t => t.2 * h t.1).sum

theorem coefN_eq (f : Lvm.Form) (c : Nat) : coefN f c = lfE (fun l => if l = [c] then 1 else 0) f := by
  unfold coefN lfE
  rw [Lvm.Har.sumE_eq_sum]
  generalize f.terms = ts
  induction ts with
  | nil => simp
  | cons t ts ih => by_cases h : t.1 = [c] <;> simp [List.filter_cons, h, ih]

/-- The constant part's `h` of table `ot` at `pt` (`constN`'s summand). -/
def hT (ot : Option Tab) (pt : List FE) : List Nat → FE
  | [] => 1
  | [c] => match ot with
    | some t => match t.cols[c]? with
      | some (.fix _ ev) => ev (pt.take t.τ)
      | _ => 0
    | none => 0
  | _ => 0

theorem constN_eq (t : Tab) (f : Lvm.Form) (pt : List FE) : constN t f (pt.take t.τ) = lfE (hT (some t) pt) f := by
  unfold constN lfE
  rw [Lvm.Har.sumE_eq_sum]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rcases m with ⟨_ | ⟨c, _ | ⟨d, l⟩⟩, x⟩
  · simp [hT]
  · simp only [hT]
    rcases t.cols[c]? with _ | (⟨_, _⟩ | ⟨_, _⟩) <;> simp
  · simp [hT]

theorem lfE_formSum (h : List Nat → FE) (fs : List Lvm.Form) : lfE h (formSum fs) = (fs.map (lfE h)).sum := by
  induction fs with
  | nil => simp [lfE, formSum]
  | cons f fs ih =>
    simp only [lfE, formSum, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem lfE_const (h : List Nat → FE) (x : FE) : lfE h (Lvm.Form.const x) = x * h [] := by
  simp [lfE, Lvm.Form.const]

theorem lfE_cpolyForm (h : List Nat → FE) (w : FE) (P : CPoly) :
    lfE h (cpolyForm w P) = (P.map fun m => w * FE.ofK m.1 * h m.2).sum := by
  simp only [lfE, cpolyForm, List.map_map]
  rfl

theorem lfE_col (h : List Nat → FE) (c : Nat) : lfE h (Lvm.Form.col c) = h [c] := by
  simp [lfE, Lvm.Form.col, gpow]

theorem sum_monsAt (F : LMon → FE) (i : Nat) (P : CPoly) :
    ((monsAt i P).map F).sum = (P.map fun m => F (i, m.1, m.2)).sum := by
  simp [monsAt, Function.comp_def]

/-- **A leaf form under `h`**: its constant term, then its monomials (`leafMons`), each at its slot's `eq(α, i)`. -/
theorem lfE_leafForm (h : List Nat → FE) (eqα : List FE) (β : FE) (b : SBlk) (push : Bool) :
    lfE h (leafForm eqα β b.key (if push then cntPush b else CPoly.var b.col)) =
      (β + eqα.getD 0 0 * FE.ofK b.key.sep) * h [] +
        ((leafMons b push).map fun m => eqα.getD m.1 0 * FE.ofK m.2.1 * h m.2.2).sum := by
  rw [leafForm, lfE_formSum, leafMons]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    lfE_const, lfE_cpolyForm, sum_monsAt, List.map_map, Function.comp_def, add_zero]
  have hv : ∀ l : List (CPoly × Nat),
      (l.map fun x => (x.1.map fun m => eqα.getD (3 + x.2) 0 * FE.ofK m.1 * h m.2).sum).sum =
        ((l.flatMap fun x => monsAt (3 + x.2) x.1).map fun m => eqα.getD m.1 0 * FE.ofK m.2.1 * h m.2.2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append, ih, sum_monsAt]
  rw [← hv]
  ring

/-! ## Static stacking -/

theorem stackG_fst {α : Type} (κ : α → Nat) (l : List α) :
    (stackG κ l).map Prod.fst = l.mergeSort fun a b => decide (κ b ≤ κ a) := by
  unfold stackG
  generalize l.mergeSort (fun a b => decide (κ b ≤ κ a)) = m
  suffices h : ∀ (acc : List (α × Nat)) (c : Nat),
      (m.foldl (fun (acc : List (α × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ κ b)) (acc, c)).1.map
        Prod.fst = acc.map Prod.fst ++ m by simpa using h [] 0
  induction m with
  | nil => intro acc c; simp
  | cons b m ih => intro acc c; simp only [List.foldl_cons]; rw [ih]; simp

theorem mem_stackG {α : Type} (κ : α → Nat) (l : List α) (a : α) : a ∈ l ↔ ∃ x ∈ stackG κ l, x.1 = a := by
  rw [← List.mem_mergeSort (le := fun a b => decide (κ b ≤ κ a)), ← stackG_fst, List.mem_map]

theorem ppOfShape_tab {t : TShape} {j : Nat} {b : SBlk} (h : b ∈ ppOfShape t j) : b.tab = j := by
  simp only [ppOfShape, List.mem_append, List.mem_map] at h
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem ppS_tab_lt (S : List TShape) : ∀ bo ∈ ppS S, bo.1.tab < S.length := by
  intro bo hbo
  have hb : bo.1 ∈ ppBlocks S := (mem_stackG SBlk.κ _ _).mpr ⟨bo, hbo, rfl⟩
  simp only [ppBlocks, List.mem_flatMap] at hb
  obtain ⟨tj, htj, hb⟩ := hb
  rw [ppOfShape_tab hb]
  simpa using List.snd_lt_of_mem_zipIdx htj

theorem cS_tab_lt (S : List TShape) : ∀ bo ∈ cS S, bo.1.1 < S.length := by
  intro bo hbo
  have hb : bo.1 ∈ cBlocks S := (mem_stackG (fun c : Nat × Nat × Nat => c.2.1) _ _).mpr ⟨bo, hbo, rfl⟩
  simp only [cBlocks, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨tj, htj, c, -, hc⟩ := hb
  rw [← hc]
  simpa using List.snd_lt_of_mem_zipIdx htj

/-- The push/pull blocks of table `j` are its reads and seeds. -/
theorem exists_ppS (S : List TShape) {j : Nat} (hj : j < S.length) (P : SBlk → Prop) :
    (∃ x ∈ ppS S, x.1.tab = j ∧ P x.1) ↔ ∃ b ∈ ppOfShape S[j] j, P b := by
  constructor
  · rintro ⟨x, hx, htab, hP⟩
    have hb : x.1 ∈ ppBlocks S := (mem_stackG SBlk.κ _ _).mpr ⟨x, hx, rfl⟩
    simp only [ppBlocks, List.mem_flatMap] at hb
    obtain ⟨⟨t, j'⟩, htj, hb⟩ := hb
    have hj' := ppOfShape_tab hb
    rw [htab] at hj'
    subst hj'
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hj, Option.some.injEq] at htj
    subst htj
    exact ⟨x.1, hb, hP⟩
  · rintro ⟨b, hb, hP⟩
    have hb' : b ∈ ppBlocks S := by
      simp only [ppBlocks, List.mem_flatMap]
      exact ⟨(S[j], j), List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj), hb⟩
    obtain ⟨x, hx, rfl⟩ := (mem_stackG SBlk.κ _ _).mp hb'
    exact ⟨x, hx, ppOfShape_tab hb, hP⟩

/-- The count blocks of table `j` are its read counts. -/
theorem exists_cS (S : List TShape) {j : Nat} (hj : j < S.length) (c : Nat) :
    (∃ x ∈ cS S, x.1.1 = j ∧ x.1.2.2 = c) ↔ c ∈ countsS S[j] := by
  constructor
  · rintro ⟨x, hx, htab, hc⟩
    have hb : x.1 ∈ cBlocks S := (mem_stackG (fun c : Nat × Nat × Nat => c.2.1) _ _).mpr ⟨x, hx, rfl⟩
    simp only [cBlocks, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨⟨t, j'⟩, htj, c', hc', he⟩ := hb
    rw [← he] at htab hc
    simp only at htab hc
    subst htab hc
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hj, Option.some.injEq] at htj
    subst htj
    exact hc'
  · intro hc
    have hb : (j, S[j].τ, c) ∈ cBlocks S := by
      simp only [cBlocks, List.mem_flatMap, List.mem_map]
      exact ⟨(S[j], j), List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj), c, hc, rfl⟩
    obtain ⟨x, hx, hxe⟩ := (mem_stackG (fun c : Nat × Nat × Nat => c.2.1) _ _).mp hb
    exact ⟨x, hx, by rw [hxe], by rw [hxe]⟩

/-! ## The spec side: `busFinalR`'s forms under linear functionals -/

theorem forms_getD' (st : List Tab) (i : BusIn) {j : Nat} (hj : j < st.length) :
    (busFinalR st i).forms.getD j [] = (sidesR st i).map fun s => (⟨bucketN s j⟩ : Lvm.Form) := by
  have hl : j < ((List.range st.length).map fun j => ((sidesR st i).map (bucketR st.length)).map
      fun a => (⟨a.getD j []⟩ : Lvm.Form)).length := by rw [List.length_map, List.length_range]; exact hj
  rw [busFinalR_forms_def, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range, List.map_map]
  exact List.map_congr_left fun s _ => by simp only [Function.comp_apply, bucketR_getD _ _ hj]

theorem lfE_bucketN (h : List Nat → FE) (s : List (NBlock × FE)) (j : Nat) :
    lfE h ⟨bucketN s j⟩ = ((s.filter fun bw => bw.1.tab == j).map fun bw => bw.2 * lfE h bw.1.form).sum := by
  unfold lfE bucketN
  rw [sum_flatMap', List.map_reverse, List.sum_reverse]
  congr 1
  refine List.map_congr_left fun bw _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun t _ => by simp only [Function.comp_apply]; ring)

theorem lf_side (st : List Tab) (i : BusIn) (h : List Nat → FE) {j : Nat} (hj : j < st.length) :
    (lfE h (formN (busFinalR st i) j 0) = (((ppS (st.map Tab.shape)).filter fun bo => bo.1.tab == j).map fun bo =>
        blockWeight i.point bo.1.κ bo.2 * lfE h (fPush (eqKernel i.alphas) i.beta bo.1).form).sum) ∧
    (lfE h (formN (busFinalR st i) j 1) = (((ppS (st.map Tab.shape)).filter fun bo => bo.1.tab == j).map fun bo =>
        blockWeight i.point bo.1.κ bo.2 * lfE h (fPull (eqKernel i.alphas) i.beta bo.1).form).sum) ∧
    (lfE h (formN (busFinalR st i) j 2) = (((cS (st.map Tab.shape)).filter fun bo => bo.1.1 == j).map fun bo =>
        blockWeight i.point bo.1.2.1 bo.2 * h [bo.1.2.2]).sum) := by
  simp only [formN, forms_getD' st i hj, sidesR_eq, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, lfE_bucketN]
  refine ⟨?_, ?_, ?_⟩
  · rw [filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl)]; rfl
  · rw [filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl)]; rfl
  · rw [filter_map_tab _ _ (fun bo : (Nat × Nat × Nat) × Nat => bo.1.1) (fun _ => rfl)]
    simp only [Function.comp_def, fCnt, lfE_col]

theorem lf_pp (st : List Tab) (i : BusIn) (h : List Nat → FE) {j : Nat} (hj : j < st.length) {s : Nat}
    (hs : s < 2) :
    lfE h (formN (busFinalR st i) j s) = (((ppS (st.map Tab.shape)).filter fun bo => bo.1.tab == j).map fun bo =>
        blockWeight i.point bo.1.κ bo.2 * ((i.beta + (eqKernel i.alphas).getD 0 0 * FE.ofK bo.1.key.sep) * h [] +
          ((leafMons bo.1 (decide (s = 0))).map fun m =>
            (eqKernel i.alphas).getD m.1 0 * FE.ofK m.2.1 * h m.2.2).sum)).sum := by
  obtain ⟨h0, h1, -⟩ := lf_side st i h hj
  rcases s with _ | _ | s
  · rw [h0]
    exact congrArg List.sum (List.map_congr_left fun bo _ => congrArg _ (lfE_leafForm h _ _ bo.1 true))
  · rw [h1]
    exact congrArg List.sum (List.map_congr_left fun bo _ => congrArg _ (lfE_leafForm h _ _ bo.1 false))
  · omega

theorem sum_zipIdx_snd {α : Type} (l : List α) (H : Nat → FE) :
    (l.zipIdx.map fun tj => H tj.2).sum = ((List.range l.length).map H).sum := by
  rw [show (fun tj : α × Nat => H tj.2) = H ∘ Prod.snd from rfl, ← List.map_map, List.zipIdx_map_snd,
    List.range_eq_range']

/-- **Side `s`'s spec value** (push or pull): the total, then every block's constant at its weight. -/
theorem value_pp (tabs : List Tab) (i : BusIn) {s : Nat} (hs : s < 2) :
    mbValueN tabs (busFinalR tabs i) i.point s = i.values.getD s 0 + 1 +
      ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum +
      ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2 *
        ((i.beta + (eqKernel i.alphas).getD 0 0 * FE.ofK bo.1.key.sep) +
          ((leafMons bo.1 (decide (s = 0))).map fun m => (eqKernel i.alphas).getD m.1 0 * FE.ofK m.2.1 *
            hT tabs[bo.1.tab]? i.point m.2.2).sum)).sum := by
  unfold mbValueN
  rw [totals_eq]
  simp only [Lvm.Har.sumE_eq_sum]
  have htot : [i.values.getD 0 0 + 1 + ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum,
       i.values.getD 1 0 + 1 + ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum,
       i.values.getD 2 0 + 1 + ((cS (tabs.map Tab.shape)).map fun bo =>
        blockWeight i.point bo.1.2.1 bo.2).sum].getD s 0 = i.values.getD s 0 + 1 +
      ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum := by
    rcases s with _ | _ | s
    · rfl
    · rfl
    · omega
  rw [htot]
  congr 1
  set G : SBlk × Nat → FE := fun bo => blockWeight i.point bo.1.κ bo.2 *
    ((i.beta + (eqKernel i.alphas).getD 0 0 * FE.ofK bo.1.key.sep) +
      ((leafMons bo.1 (decide (s = 0))).map fun m => (eqKernel i.alphas).getD m.1 0 * FE.ofK m.2.1 *
        hT tabs[bo.1.tab]? i.point m.2.2).sum) with hG
  have e : ∀ tj ∈ tabs.zipIdx, (match tj with | (t, j) => constN t (formN (busFinalR tabs i) j s) (i.point.take t.τ)) =
      (((ppS (tabs.map Tab.shape)).filter fun bo => bo.1.tab == tj.2).map G).sum := by
    rintro ⟨t, j⟩ htj
    have hj : j < tabs.length := by simpa using List.snd_lt_of_mem_zipIdx htj
    have ht : tabs[j]? = some t := List.mem_zipIdx_iff_getElem?.mp htj
    show constN t (formN (busFinalR tabs i) j s) (i.point.take t.τ) = _
    rw [constN_eq, lf_pp tabs i _ hj hs]
    refine congrArg List.sum (List.map_congr_left fun bo hbo => ?_)
    have hb : bo.1.tab = j := by simpa using (List.mem_filter.mp hbo).2
    simp only [hG, hb, ht, hT, mul_one]
  rw [List.map_congr_left e, sum_zipIdx_snd tabs (fun j => (((ppS (tabs.map Tab.shape)).filter
    fun bo => bo.1.tab == j).map G).sum)]
  exact sum_group (fun bo : SBlk × Nat => bo.1.tab) G _ List.nodup_range _ fun bo hbo =>
    List.mem_range.mpr (by simpa using ppS_tab_lt _ bo hbo)

/-- **The count side's spec value**: the total (no read count column is fixed). -/
theorem value_cnt (tabs : List Tab) (i : BusIn)
    (hcnt : ∀ t ∈ tabs, ∀ r ∈ t.reads, ∀ f e, t.cols[r.2]? ≠ some (.fix f e)) :
    mbValueN tabs (busFinalR tabs i) i.point 2 = i.values.getD 2 0 + 1 +
      ((cS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.2.1 bo.2).sum := by
  unfold mbValueN
  rw [totals_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero, Lvm.Har.sumE_eq_sum]
  rw [List.sum_eq_zero (l := List.map _ tabs.zipIdx), add_zero]
  intro x hx
  obtain ⟨⟨t, j⟩, htj, rfl⟩ := List.mem_map.mp hx
  have hj : j < tabs.length := by simpa using List.snd_lt_of_mem_zipIdx htj
  have ht : tabs[j]? = some t := List.mem_zipIdx_iff_getElem?.mp htj
  have htm : t ∈ tabs := List.mem_of_getElem? ht
  show constN t (formN (busFinalR tabs i) j 2) (i.point.take t.τ) = 0
  rw [constN_eq, (lf_side tabs i _ hj).2.2]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hbo, hbj⟩ := List.mem_filter.mp hbo
  have hjS : j < (tabs.map Tab.shape).length := by simpa using hj
  have hc : bo.1.2.2 ∈ countsS (tabs.map Tab.shape)[j] :=
    (exists_cS _ hjS _).mp ⟨bo, hbo, by simpa using hbj, rfl⟩
  have htj' : (tabs.map Tab.shape)[j] = t.shape := by
    simp [List.getElem_map, (List.getElem?_eq_some_iff.mp ht).2]
  rw [htj', countsS, List.mem_filterMap] at hc
  obtain ⟨r, hr, hrc⟩ := hc
  have hrc' : r.2 = bo.1.2.2 := by
    split at hrc
    · exact Option.some.inj hrc
    · exact absurd hrc (by simp)
  have hnf := hcnt t htm r (by simpa [Tab.shape] using hr)
  rw [hrc'] at hnf
  have h0 : hT (some t) i.point [bo.1.2.2] = 0 := by
    show (match t.cols[bo.1.2.2]? with | some (.fix _ ev) => ev (i.point.take t.τ) | _ => 0) = 0
    cases hcol : t.cols[bo.1.2.2]? with
    | none => rfl
    | some cs => cases cs with
      | com _ _ => rfl
      | fix f ev => exact absurd hcol (hnf f ev)
  rw [h0, mul_zero]

theorem coef_pp (tabs : List Tab) (i : BusIn) {j : Nat} (hj : j < tabs.length) {s : Nat} (hs : s < 2) (c : Nat) :
    coefN (formN (busFinalR tabs i) j s) c = (((ppS (tabs.map Tab.shape)).filter fun bo => bo.1.tab == j).map fun bo =>
      blockWeight i.point bo.1.κ bo.2 * ((leafMons bo.1 (decide (s = 0))).map fun m =>
        if m.2.2 = [c] then (eqKernel i.alphas).getD m.1 0 * FE.ofK m.2.1 else 0).sum).sum := by
  rw [coefN_eq, lf_pp tabs i _ hj hs]
  refine congrArg List.sum (List.map_congr_left fun bo _ => ?_)
  rw [if_neg (by simp), mul_zero, zero_add]
  refine congrArg (fun x => _ * x) (congrArg List.sum (List.map_congr_left fun m _ => ?_))
  split <;> simp

theorem coef_cnt (tabs : List Tab) (i : BusIn) {j : Nat} (hj : j < tabs.length) (c : Nat) :
    coefN (formN (busFinalR tabs i) j 2) c = (((cS (tabs.map Tab.shape)).filter fun bo => bo.1.1 == j).map fun bo =>
      if bo.1.2.2 = c then blockWeight i.point bo.1.2.1 bo.2 else 0).sum := by
  rw [coefN_eq, (lf_side tabs i _ hj).2.2]
  refine congrArg List.sum (List.map_congr_left fun bo _ => ?_)
  by_cases h : bo.1.2.2 = c <;> simp [h]

/-! ## The gadget's pieces -/

section circ
variable {c : Ctx} {M : Mem}

theorem soundG_seqAll {α β : Type} (g : β → BM α) (P : β → α → Prop) :
    ∀ l : List β, (∀ b ∈ l, SoundG c M (g b) (P b)) →
      SoundG c M (seqAll (l.map g)) fun r => List.Forall₂ P l r
  | [], _ => soundG_pure List.Forall₂.nil
  | b :: l, h => soundG_bind (h b List.mem_cons_self) fun x hx =>
      soundG_bind (soundG_seqAll g P l fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) fun xs hxs =>
        soundG_pure (List.Forall₂.cons hx hxs)

theorem soundG_foldlM {β : Type} (step : Cell → β → BM Cell) (g : β → FE) :
    ∀ (l : List β) (start : Cell), (∀ b ∈ l, ∀ acc, SoundG c M (step acc b) fun r => r.val M = acc.val M + g b) →
      SoundG c M (l.foldlM step start) fun r => r.val M = start.val M + (l.map g).sum
  | [], start, _ => by rw [List.foldlM_nil]; exact soundG_pure (by simp)
  | b :: l, start, h => by
    rw [List.foldlM_cons]
    exact soundG_bind (h b List.mem_cons_self start) fun x hx =>
      soundG_mono (soundG_foldlM step g l x fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) fun r hr => by
        rw [hr, hx, List.map_cons, List.sum_cons]; ring

theorem coefG_sound {z : Cell} (hz : z.val M = 0) (w : List Cell) (f : Option (Nat × FK) → Cell)
    (hf : (f none).val M = 1) (key : CKey) :
    SoundG c M (coefG z w f key) fun r => r.val M = (key.map fun t => (atC z w t.1).val M * (f t.2).val M).sum := by
  unfold coefG
  split
  · exact soundG_pure (by simp [hf])
  · refine soundG_mono (soundG_foldlM _ (fun t => (atC z w t.1).val M * (f t.2).val M) _ z ?_) fun r hr => by
      rw [hr, hz, zero_add]
    rintro ⟨j, _ | y⟩ _ acc
    · exact soundG_mono (soundG_aspec (QB.aspec_lin _ 1 0 acc (atC z w j))) fun r hr => by
        rw [hr.1, hf, ofK_one, ofK_zero]; ring
    · exact soundG_mono (soundG_aspec (QB.aspec_mulAdd .E (atC z w j) (f (some y)) acc)) fun r hr => by
        rw [hr.1]; ring

theorem k0G_sound (be : Cell) (eb : Nat) (k : K0Key) :
    SoundG c M (k0G be eb k) fun r => r.val M = be.val M + FE.ofK k.1 * M.e eb +
      (k.2.map fun m => FE.ofK m.2 * M.e (eb + m.1)).sum := by
  unfold k0G
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E k.1 0 be (ec eb))) fun a ha => ?_
  refine soundG_mono (soundG_foldlM _ (fun m => FE.ofK m.2 * M.e (eb + m.1)) k.2 a fun m _ acc =>
    soundG_mono (soundG_aspec (QB.aspec_lin .E m.2 0 acc (ec (eb + m.1)))) fun r hr => by
      rw [hr.1, Cell.val_E, ofK_zero, add_zero]) fun r hr => ?_
  rw [hr, ha.1, Cell.val_E, ofK_zero, add_zero]

theorem valG_sound {z : Cell} (hz : z.val M = 0) (be : Cell) (eb : Nat) (spp : Cell) (ws pw gs : List Cell)
    (wsP : List (List Nat)) (powP : List (Nat × Nat)) (gsP : List (List (Nat × Nat)))
    (f : Option (Nat × FK) → Cell) (v : Cell) (cp : List (K0Key × List Nat) × List FxKey) :
    SoundG c M (do
      let t ← lin .E 1 1 v spp
      let t ← cp.1.foldlM (fun acc k => do
        let c ← k0G be eb k.1
        mulAdd .E c (atC z ws (wsP.idxOf k.2)) acc) t
      cp.2.foldlM (fun acc g => do
        let pg ← mulAdd .E (atC z pw (powP.idxOf (g.1.2.2.1, g.1.2.2.2))) (atC z gs (gsP.idxOf g.2)) z
        mulAdd .E (f (some (g.1.1, g.1.2.1))) pg acc) t) fun r =>
      r.val M = v.val M + spp.val M + 1 +
        (cp.1.map fun k => (be.val M + FE.ofK k.1.1 * M.e eb +
          (k.1.2.map fun m => FE.ofK m.2 * M.e (eb + m.1)).sum) * (atC z ws (wsP.idxOf k.2)).val M).sum +
        (cp.2.map fun g => (f (some (g.1.1, g.1.2.1))).val M *
          ((atC z pw (powP.idxOf (g.1.2.2.1, g.1.2.2.2))).val M * (atC z gs (gsP.idxOf g.2)).val M)).sum := by
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 v spp)) fun t ht => ?_
  refine soundG_bind (soundG_foldlM _ (fun k => (be.val M + FE.ofK k.1.1 * M.e eb +
      (k.1.2.map fun m => FE.ofK m.2 * M.e (eb + m.1)).sum) * (atC z ws (wsP.idxOf k.2)).val M) cp.1 t
    fun k _ acc => soundG_bind (k0G_sound be eb k.1) fun c hc =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E c _ acc)) fun r hr => by rw [hr.1, hc]; ring) fun t2 ht2 => ?_
  refine soundG_mono (soundG_foldlM _ (fun g => (f (some (g.1.1, g.1.2.1))).val M *
      ((atC z pw (powP.idxOf (g.1.2.2.1, g.1.2.2.2))).val M * (atC z gs (gsP.idxOf g.2)).val M)) cp.2 t2
    fun g _ acc => soundG_bind (soundG_aspec (QB.aspec_mulAdd .E _ _ z)) fun pg hpg =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E _ pg acc)) fun r hr => by rw [hr.1, hpg.1, hz]; ring)
    fun r hr => ?_
  rw [hr, ht2, ht.1, ofK_one]; ring

theorem ekC_val {z : Cell} (eb : Nat) (ekP : List (Nat × FK)) (ek : List Cell)
    (hek : List.Forall₂ (fun x (r : Cell) => r.val M = FE.ofK x.2 * M.e (eb + x.1)) ekP ek)
    (y : Nat × FK) (hy : y.2 = 1 ∨ y ∈ ekP) : (ekC z eb ekP ek y).val M = FE.ofK y.2 * M.e (eb + y.1) := by
  unfold ekC
  by_cases h1 : y.2 = 1
  · rw [if_pos (by simp [h1]), h1, ofK_one, one_mul]; rfl
  · rw [if_neg (by simpa using h1)]
    have hi := List.idxOf_lt_length_of_mem (hy.resolve_left h1)
    have := f2_getD hek z _ hi
    rw [List.getElem_idxOf hi] at this
    exact this

end circ

/-! ## The plan against the spec: the parts -/

theorem exists_zipIdx {α : Type} (l : List α) (R : α → Prop) : (∃ y ∈ l.zipIdx, R y.1) ↔ ∃ a ∈ l, R a := by
  constructor
  · rintro ⟨y, hy, hR⟩; exact ⟨y.1, List.fst_mem_of_mem_zipIdx hy, hR⟩
  · rintro ⟨a, ha, hR⟩
    have : a ∈ l.zipIdx.map Prod.fst := by rw [List.zipIdx_map_fst]; exact ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp this
    exact ⟨y, hy, hR⟩

theorem ppS_mem {S : List TShape} {bo : SBlk × Nat} (h : bo ∈ ppS S) :
    ∃ j, ∃ hj : j < S.length, bo.1 ∈ ppOfShape S[j] j := by
  have hb : bo.1 ∈ ppBlocks S := (mem_stackG SBlk.κ _ _).mpr ⟨bo, h, rfl⟩
  simp only [ppBlocks, List.mem_flatMap] at hb
  obtain ⟨⟨t, j⟩, htj, hb⟩ := hb
  have hj : j < S.length := by simpa using List.snd_lt_of_mem_zipIdx htj
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hj, Option.some.injEq] at htj
  subst htj
  exact ⟨j, hj, hb⟩

/-- A block's key is a key of its table. -/
theorem ppS_key (tabs : List Tab) {bo : SBlk × Nat} (h : bo ∈ ppS (tabs.map Tab.shape)) :
    ∃ t, tabs[bo.1.tab]? = some t ∧ bo.1.key ∈ t.reads.map (·.1) ++ t.seeds.map (·.1) := by
  obtain ⟨j, hj, hb⟩ := ppS_mem h
  have hj' : j < tabs.length := by simpa using hj
  refine ⟨tabs[j], by rw [ppOfShape_tab hb, List.getElem?_eq_getElem hj'], ?_⟩
  simp only [List.getElem_map, ppOfShape, Tab.shape, List.mem_append, List.mem_map] at hb
  rcases hb with ⟨r, hr, he⟩ | ⟨s, hs, he⟩
  · rw [← he]; exact List.mem_append_left _ (List.mem_map_of_mem hr)
  · rw [← he]; exact List.mem_append_right _ (List.mem_map_of_mem hs)

theorem slot_lt (b : SBlk) (push : Bool) : ∀ m ∈ leafMons b push, m.1 < 3 + b.key.val.length := by
  intro m hm
  simp only [leafMons, monsAt, List.mem_append, List.mem_map, List.mem_flatMap] at hm
  rcases hm with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨⟨P, l⟩, hPl, _, _, rfl⟩
  · show 1 < _; omega
  · show 2 < _; omega
  · have := List.snd_lt_of_mem_zipIdx hPl
    simp only at this ⊢
    omega

/-- A key names column `c` (in a monomial `[c]`). -/
def KC (k : Key) (c : Nat) : Prop := (∃ mm ∈ k.addr, mm.2 = [c]) ∨ ∃ P ∈ k.val, ∃ mm ∈ P, mm.2 = [c]

theorem leafMons_col (b : SBlk) (push : Bool) (c : Nat) :
    (∃ m ∈ leafMons b push, m.2.2 = [c]) ↔
      KC b.key c ∨ ∃ mm ∈ (if push then cntPush b else CPoly.var b.col), mm.2 = [c] := by
  unfold leafMons KC
  constructor
  · rintro ⟨m, hm, hc⟩
    simp only [monsAt, List.mem_append, List.mem_map, List.mem_flatMap] at hm
    rcases hm with (⟨mm, hmm, rfl⟩ | ⟨mm, hmm, rfl⟩) | ⟨⟨P, l⟩, hPl, mm, hmm, rfl⟩
    · exact Or.inl (Or.inl ⟨mm, hmm, hc⟩)
    · exact Or.inr ⟨mm, hmm, hc⟩
    · exact Or.inl (Or.inr ⟨P, List.fst_mem_of_mem_zipIdx hPl, mm, hmm, hc⟩)
  · rintro ((⟨mm, hmm, hc⟩ | ⟨P, hP, mm, hmm, hc⟩) | ⟨mm, hmm, hc⟩)
    · exact ⟨(1, mm.1, mm.2), by simp only [monsAt, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨mm, hmm, rfl⟩), hc⟩
    · obtain ⟨y, hy, hyP⟩ := (exists_zipIdx b.key.val (· = P)).mpr ⟨P, hP, rfl⟩
      refine ⟨(3 + y.2, mm.1, mm.2), ?_, hc⟩
      simp only [monsAt, List.mem_append, List.mem_map, List.mem_flatMap]
      exact Or.inr ⟨y, hy, mm, by rw [hyP]; exact hmm, rfl⟩
    · exact ⟨(2, mm.1, mm.2), by simp only [monsAt, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨mm, hmm, rfl⟩), hc⟩

theorem cnt_col (b : SBlk) (push : Bool) (c : Nat) :
    (∃ mm ∈ (if push then cntPush b else CPoly.var b.col), mm.2 = [c]) ↔
      (if push then b.rd = true ∧ b.col = c else b.col = c) := by
  cases push <;> cases h : b.rd <;> simp [cntPush, CPoly.var, CPoly.const, h, eq_comm]

theorem lin_col {P : CPoly} (hP : cpolyLinB P = true) (c : Nat) : (∃ mm ∈ P, mm.2 = [c]) ↔ c ∈ P.flatMap (·.2) := by
  unfold cpolyLinB at hP
  rw [List.all_eq_true] at hP
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨mm, h, he⟩; exact ⟨mm, h, by simp [he]⟩
  · rintro ⟨mm, h, hc⟩
    have hl := hP mm h
    refine ⟨mm, h, ?_⟩
    rcases mm with ⟨k, _ | ⟨a, _ | ⟨b, l⟩⟩⟩
    · simp at hc
    · simp at hc ⊢; exact hc.symm
    · simp at hl

theorem key_cols {k : Key} (hk : (cpolyLinB k.addr && k.val.all cpolyLinB) = true) (c : Nat) :
    KC k c ↔ c ∈ (k.addr :: k.val).flatMap fun P => P.flatMap (·.2) := by
  rw [Bool.and_eq_true, List.all_eq_true] at hk
  unfold KC
  rw [List.flatMap_cons, List.mem_append]
  refine or_congr (lin_col hk.1 c) ?_
  rw [List.mem_flatMap]
  exact ⟨fun ⟨P, hP, h⟩ => ⟨P, hP, (lin_col (hk.2 P hP) c).mp h⟩,
    fun ⟨P, hP, h⟩ => ⟨P, hP, (lin_col (hk.2 P hP) c).mpr h⟩⟩

theorem bex_congr' {α : Type} {l : List α} {A B : α → Prop} (h : ∀ a ∈ l, A a ↔ B a) :
    (∃ a ∈ l, A a) ↔ ∃ a ∈ l, B a :=
  ⟨fun ⟨a, ha, h'⟩ => ⟨a, ha, (h a ha).mp h'⟩, fun ⟨a, ha, h'⟩ => ⟨a, ha, (h a ha).mpr h'⟩⟩

theorem bex_or {α : Type} {l : List α} {A B : α → Prop} :
    (∃ a ∈ l, A a ∨ B a) ↔ (∃ a ∈ l, A a) ∨ ∃ a ∈ l, B a :=
  ⟨fun ⟨a, ha, h⟩ => h.elim (fun h => Or.inl ⟨a, ha, h⟩) (fun h => Or.inr ⟨a, ha, h⟩),
    fun h => h.elim (fun ⟨a, ha, h⟩ => ⟨a, ha, Or.inl h⟩) (fun ⟨a, ha, h⟩ => ⟨a, ha, Or.inr h⟩)⟩

theorem exists_ppOfShape (t : Tab) (j : Nat) (P : SBlk → Prop) :
    (∃ b ∈ ppOfShape t.shape j, P b) ↔
      (∃ r ∈ t.reads, P ⟨j, t.τ, r.1, true, r.2⟩) ∨ ∃ x ∈ t.seeds, P ⟨j, t.τ, x.1, false, x.2⟩ := by
  unfold ppOfShape Tab.shape
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ⟨b, (⟨r, hr, rfl⟩ | ⟨x, hx, rfl⟩), h⟩
    · exact Or.inl ⟨r, hr, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨r, hr, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨_, Or.inl ⟨r, hr, rfl⟩, h⟩
    · exact ⟨_, Or.inr ⟨x, hx, rfl⟩, h⟩

theorem mem_keyCols (t : Tab) (F : Key → List Nat) (c : Nat) :
    c ∈ (t.reads.map (·.1) ++ t.seeds.map (·.1)).flatMap F ↔ (∃ r ∈ t.reads, c ∈ F r.1) ∨ ∃ x ∈ t.seeds, c ∈ F x.1 := by
  simp only [List.mem_flatMap, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨k, (⟨r, hr, rfl⟩ | ⟨x, hx, rfl⟩), h⟩
    · exact Or.inl ⟨r, hr, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨r, hr, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨r.1, Or.inl ⟨r, hr, rfl⟩, h⟩
    · exact ⟨x.1, Or.inr ⟨x, hx, rfl⟩, h⟩

theorem mem_map_snd (l : List (Key × Nat)) (c : Nat) : c ∈ l.map (·.2) ↔ ∃ r ∈ l, r.2 = c := by
  simp only [List.mem_map]

/-- **A side names column `c` of table `t` iff one of its blocks has a monomial `[c]`** (MB-LIN keys). -/
theorem sideCols_iff (t : Tab)
    (hk : ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), (cpolyLinB k.addr && k.val.all cpolyLinB) = true)
    (j : Nat) {s : Nat} (hs : s < 2) {c : Nat} (hc : c < t.w) :
    (∃ b ∈ ppOfShape t.shape j, ∃ m ∈ leafMons b (decide (s = 0)), m.2.2 = [c]) ↔ c ∈ sideColsL t s := by
  have hkr : ∀ r ∈ t.reads, KC r.1 c ↔ c ∈ (r.1.addr :: r.1.val).flatMap fun P => P.flatMap (·.2) :=
    fun r hr => key_cols (hk r.1 (List.mem_append_left _ (List.mem_map_of_mem hr))) c
  have hks : ∀ s ∈ t.seeds, KC s.1 c ↔ c ∈ (s.1.addr :: s.1.val).flatMap fun P => P.flatMap (·.2) :=
    fun s hs => key_cols (hk s.1 (List.mem_append_right _ (List.mem_map_of_mem hs))) c
  have hRd : ∀ r : Key × Nat, (∃ m ∈ leafMons ⟨j, t.τ, r.1, true, r.2⟩ (decide (s = 0)), m.2.2 = [c]) ↔
      KC r.1 c ∨ r.2 = c := by
    intro r; rw [leafMons_col, cnt_col]; cases decide (s = 0) <;> simp
  have hSd : ∀ x : Key × Nat, (∃ m ∈ leafMons ⟨j, t.τ, x.1, false, x.2⟩ (decide (s = 0)), m.2.2 = [c]) ↔
      KC x.1 c ∨ (decide (s = 0) = false ∧ x.2 = c) := by
    intro x; rw [leafMons_col, cnt_col]; cases decide (s = 0) <;> simp
  rw [exists_ppOfShape, bex_congr' (fun r _ => hRd r), bex_congr' (fun x _ => hSd x), bex_or, bex_or,
    bex_congr' hkr, bex_congr' hks, sideColsL]
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · simp only [List.mem_filter, List.mem_range, hc, true_and, List.contains_iff_mem, ↓reduceIte,
      List.mem_append, mem_keyCols, mem_map_snd]
    constructor
    · rintro ((h | h) | (h | ⟨x, hx, h, -⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact absurd h (by decide)
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
  · simp only [List.mem_filter, List.mem_range, hc, true_and, List.contains_iff_mem, ↓reduceIte,
      Nat.one_ne_zero, List.mem_append, mem_keyCols, mem_map_snd]
    constructor
    · rintro ((h | h) | (h | ⟨x, hx, -, h⟩))
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr ⟨x, hx, h⟩
    · rintro (((h | h) | h) | ⟨x, hx, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr ⟨x, hx, rfl, h⟩)

/-- **The count side names column `c` iff a count block of table `j` is on it.** -/
theorem colKey_ne_nil_cnt (S : List TShape) {j : Nat} (hj : j < S.length) (c : Nat) :
    colKey S 2 j c ≠ [] ↔ c ∈ countsS S[j] := by
  rw [← exists_cS S hj c, colKey, if_pos rfl, cntOf, List.filterMap_map, ne_eq, List.filterMap_eq_nil_iff]
  simp only [not_forall, List.mem_filter, Function.comp_apply, ite_eq_right_iff, reduceCtorEq, imp_false,
    not_not, beq_iff_eq]
  constructor
  · rintro ⟨x, ⟨hx, hxj⟩, hc⟩; exact ⟨x.1, List.fst_mem_of_mem_zipIdx hx, hxj, hc⟩
  · rintro ⟨y, hy, hyj, hc⟩
    obtain ⟨x, hx, rfl⟩ := (exists_zipIdx (cS S) (· = y)).mpr ⟨y, hy, rfl⟩
    exact ⟨x, ⟨hx, hyj⟩, hc⟩

theorem colKey_ne_nil_pp (S : List TShape) {s : Nat} (hs : s < 2) {j : Nat} (hj : j < S.length) (c : Nat) :
    colKey S s j c ≠ [] ↔ ∃ b ∈ ppOfShape S[j] j, ∃ m ∈ leafMons b (decide (s = 0)), m.2.2 = [c] := by
  rw [← exists_ppS S hj, colKey, if_neg (by omega), ne_eq, List.flatMap_eq_nil_iff]
  simp only [List.filterMap_eq_nil_iff, ite_eq_right_iff, reduceCtorEq, imp_false, not_forall, not_not, ppOf,
    List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨_, ⟨x, ⟨hx, hxj⟩, rfl⟩, m, hm, hc⟩
    exact ⟨x.1, List.fst_mem_of_mem_zipIdx hx, hxj, m, hm, hc⟩
  · rintro ⟨y, hy, hyj, m, hm, hc⟩
    obtain ⟨x, hx, rfl⟩ := (exists_zipIdx (ppS S) (· = y)).mpr ⟨y, hy, rfl⟩
    exact ⟨_, ⟨x, ⟨hx, hyj⟩, rfl⟩, m, hm, hc⟩

/-- **The plan's columns are `sideColsL`'s**: for a committed column of table `j`, its key is nonempty iff the side
names it. -/
theorem colKey_ne_nil_iff (tabs : List Tab) (hlin : mbLinB tabs = true) {s : Nat} (hs : s < 3) {j : Nat}
    (hj : j < tabs.length) {c : Nat} (hc : c < tabs[j].w) :
    colKey (tabs.map Tab.shape) s j c ≠ [] ↔ c ∈ sideColsL tabs[j] s := by
  have hj' : j < (tabs.map Tab.shape).length := by simpa using hj
  have hS : (tabs.map Tab.shape)[j] = tabs[j].shape := List.getElem_map ..
  by_cases h2 : s = 2
  · subst h2
    rw [colKey_ne_nil_cnt _ hj', hS, ← counts_val, sideColsL]
    simp only [List.mem_filter, List.mem_range, hc, true_and, List.contains_iff_mem, if_neg (by omega : ¬ (2 = 0)),
      if_neg (by omega : ¬ (2 = 1))]
  · have hs2 : s < 2 := by omega
    rw [colKey_ne_nil_pp _ hs2 hj', hS]
    refine sideCols_iff tabs[j] ?_ j hs2 hc
    have ht := List.all_eq_true.mp hlin tabs[j] (List.getElem_mem hj)
    simp only [Bool.and_eq_true] at ht
    exact List.all_eq_true.mp ht.1.2

/-! ## The plan against the spec: coefficients and parts -/

theorem colKey_val_pp (tabs : List Tab) (i : BusIn) {s : Nat} (hs : s < 2) {j : Nat} (hj : j < tabs.length)
    (c : Nat) (wv : Nat → FE)
    (hW : ∀ x ∈ (ppS (tabs.map Tab.shape)).zipIdx, wv x.2 = blockWeight i.point x.1.1.κ x.1.2)
    (F : Option (Nat × FK) → FE)
    (hF : ∀ x ∈ ppS (tabs.map Tab.shape), x.1.tab = j → ∀ m ∈ leafMons x.1 (decide (s = 0)), m.2.2 = [c] →
      F (some (m.1, m.2.1)) = FE.ofK m.2.1 * (eqKernel i.alphas).getD m.1 0) :
    ((colKey (tabs.map Tab.shape) s j c).map fun t => wv t.1 * F t.2).sum =
      coefN (formN (busFinalR tabs i) j s) c := by
  rw [coef_pp tabs i hj hs c, colKey, if_neg (by omega), sum_flatMap', ppOf, List.map_map]
  refine sum_zipIdx_filter _ (fun bo : SBlk × Nat => bo.1.tab == j) _ _ fun x hx hxj => ?_
  simp only [Function.comp_apply]
  rw [sum_filterMap, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun m hm => ?_)
  split_ifs with h
  · simp only [Option.map_some, Option.getD_some]
    rw [hW x hx, hF x.1 (List.fst_mem_of_mem_zipIdx hx) (beq_iff_eq.mp hxj) m hm h]; ring
  · simp

theorem colKey_val_cnt (tabs : List Tab) (i : BusIn) {j : Nat} (hj : j < tabs.length) (c : Nat) (wv : Nat → FE)
    (hW : ∀ x ∈ (cS (tabs.map Tab.shape)).zipIdx,
      wv ((ppS (tabs.map Tab.shape)).length + x.2) = blockWeight i.point x.1.1.2.1 x.1.2)
    (F : Option (Nat × FK) → FE) (hF : F none = 1) :
    ((colKey (tabs.map Tab.shape) 2 j c).map fun t => wv t.1 * F t.2).sum =
      coefN (formN (busFinalR tabs i) j 2) c := by
  rw [coef_cnt tabs i hj c, colKey, if_pos rfl, cntOf, List.filterMap_map, sum_filterMap]
  refine sum_zipIdx_filter _ (fun bo : (Nat × Nat × Nat) × Nat => bo.1.1 == j) _ _ fun x hx _ => ?_
  simp only [Function.comp_apply]
  split_ifs with h
  · simp only [Option.map_some, Option.getD_some]; rw [hW x hx, hF, mul_one]
  · simp

theorem mem_partsPlan {S : List TShape} {s : Nat} {x : Nat × Nat × CKey} (h : x ∈ partsPlan S s) :
    x.1 < S.length ∧ x.2.2 = colKey S s x.1 x.2.1 := by
  simp only [partsPlan, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨⟨t, j⟩, htj, c, -, hc⟩ := h
  have hj : j < S.length := by simpa using List.snd_lt_of_mem_zipIdx htj
  split at hc
  · split at hc
    · exact absurd hc (by simp)
    · obtain rfl := Option.some.inj hc; exact ⟨hj, rfl⟩
  · exact absurd hc (by simp)

/-- **The plan's parts are `mbPartsN`'s**, given the coefficients. -/
theorem parts_eq (tabs : List Tab) (i : BusIn) (hlin : mbLinB tabs = true) {s : Nat} (hs : s < 3) (cv : CKey → FE)
    (hcv : ∀ x ∈ partsPlan (tabs.map Tab.shape) s, cv x.2.2 = coefN (formN (busFinalR tabs i) x.1 s) x.2.1) :
    (partsPlan (tabs.map Tab.shape) s).map (fun x => (cv x.2.2,
      (⟨((tabs.map Tab.shape).getD x.1 shape0).τ, (comOff ((tabs.map Tab.shape).getD x.1 shape0) x.2.1).getD 0⟩ :
        Placement), i.point.take ((tabs.map Tab.shape).getD x.1 shape0).τ)) =
      mbPartsN tabs (busFinalR tabs i) i.point s := by
  rw [List.map_congr_left (g := fun x => (coefN (formN (busFinalR tabs i) x.1 s) x.2.1,
      (⟨((tabs.map Tab.shape).getD x.1 shape0).τ, (comOff ((tabs.map Tab.shape).getD x.1 shape0) x.2.1).getD 0⟩ :
        Placement), i.point.take ((tabs.map Tab.shape).getD x.1 shape0).τ)) fun x hx => by rw [hcv x hx]]
  unfold partsPlan mbPartsN
  rw [List.map_flatMap, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun tj htj => ?_
  obtain ⟨t, j⟩ := tj
  have hj : j < tabs.length := by simpa using List.snd_lt_of_mem_zipIdx htj
  have ht : tabs[j] = t := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp htj)).2
  have hSj : (tabs.map Tab.shape).getD j shape0 = t.shape := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp [ht]
  have hrec : ∀ (c : Nat) (rec : Bool) (off : Nat), t.cols[c]? = some (ColSrc.com rec off) → rec = false := by
    intro c rec off hc
    have h1 := List.all_eq_true.mp hlin t (ht ▸ List.getElem_mem hj)
    simp only [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 _ (List.mem_of_getElem? hc)
    simpa using h2
  obtain ⟨q, hq⟩ : ∃ q, sideColsL t s = (List.range t.w).filter q := ⟨_, rfl⟩
  dsimp only [Function.comp_apply, Prod.map, id_eq]
  rw [hq, List.filterMap_filter, List.map_filterMap]
  have hw : t.shape.cols.length = t.w := by simp [Tab.shape]
  rw [hw]
  refine List.filterMap_congr fun c hc => ?_
  have hc' : c < t.w := List.mem_range.mp hc
  have hmem : q c = true ↔ c ∈ sideColsL t s := by rw [hq, List.mem_filter, List.mem_range]; simp [hc']
  have hiff := colKey_ne_nil_iff tabs hlin hs hj (c := c) (by rw [ht]; exact hc')
  rw [ht] at hiff
  obtain ⟨cs, hcs⟩ : ∃ cs, t.cols[c]? = some cs := ⟨t.cols[c], List.getElem?_eq_getElem hc'⟩
  have hgd : t.shape.cols.getD c none = colKind cs := by
    simp [Tab.shape, List.getD_eq_getElem?_getD, List.getElem?_map, hcs]
  cases cs with
  | com rec off =>
    obtain rfl := hrec c rec off hcs
    have hco : comOff t.shape c = some off := by unfold comOff; rw [hgd]; rfl
    simp only [hco, hcs]
    by_cases hk : colKey (tabs.map Tab.shape) s j c = []
    · have : ¬ q c = true := fun h => (hiff.mpr (hmem.mp h)) hk
      simp [hk, this]
    · have : q c = true := hmem.mpr (hiff.mp hk)
      rw [if_neg hk, if_pos this]
      simp only [Option.map_some, hSj, hco, Option.getD_some]
      rfl
  | fix f e =>
    have hco : comOff t.shape c = none := by unfold comOff; rw [hgd]; rfl
    simp [hco, hcs]

/-! ## The plan against the spec: the values -/

/-- `fxOf`'s summand. -/
def fxM (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) (b : SBlk) (m : LMon) : Option FxMon :=
  match m.2.2 with
    | [c] => match comOff (S.getD b.tab shape0) c with
      | some _ => none
      | none => (fix.find? fun f => f.1 == b.tab && f.2.1 == c).map fun f =>
        (m.1, m.2.1, f.2.2.1, f.2.2.2, (S.getD b.tab shape0).τ)
    | _ => none

theorem fxOf_eq (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) (b : SBlk) (push : Bool) :
    fxOf S fix b push = (leafMons b push).filterMap (fxM S fix b) := rfl

/-- Every listed fixed column is a fixed column with its power closed form (RE-FREEZE R3, H3). -/
def FixExact (tabs : List Tab) (fix : List (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ f ∈ fix, ∃ t fn e, tabs[f.1]? = some t ∧ t.cols[f.2.1]? = some (.fix fn e) ∧
    ∀ r, e r = FE.ofK (FK.x ^ f.2.2.1) * powEval r (FK.x ^ f.2.2.2)

theorem find_none {tabs : List Tab} {fix : List (Nat × Nat × Nat × Nat)} (hfx : FixExact tabs fix) {j c : Nat}
    {t : Tab} (ht : tabs[j]? = some t) (hnf : ∀ fn e, t.cols[c]? ≠ some (.fix fn e)) :
    fix.find? (fun f => f.1 == j && f.2.1 == c) = none := by
  rw [List.find?_eq_none]
  intro f hf hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨t', fn, e, ht', hc', -⟩ := hfx f hf
  rw [hp.1, ht, Option.some.injEq] at ht'
  subst ht'
  rw [hp.2] at hc'
  exact hnf fn e hc'

theorem find_some {tabs : List Tab} {fix : List (Nat × Nat × Nat × Nat)} (hfix : FixListed tabs fix)
    (hfx : FixExact tabs fix) {j c : Nat} {t : Tab} (ht : tabs[j]? = some t) {fn : Nat → FK} {e : List FE → FE}
    (hcs : t.cols[c]? = some (.fix fn e)) :
    ∃ f, fix.find? (fun f => f.1 == j && f.2.1 == c) = some f ∧
      ∀ r, e r = FE.ofK (FK.x ^ f.2.2.1) * powEval r (FK.x ^ f.2.2.2) := by
  obtain ⟨b0, s0, hm, -⟩ := hfix j t ht c fn e hcs
  cases hf : fix.find? (fun f => f.1 == j && f.2.1 == c) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ hm)
  | some f =>
    refine ⟨f, rfl, ?_⟩
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨t', fn', e', ht', hc', he'⟩ := hfx f (List.mem_of_find?_eq_some hf)
    rw [hp.1, ht, Option.some.injEq] at ht'
    subst ht'
    rw [hp.2, hcs, Option.some.injEq, ColSrc.fix.injEq] at hc'
    obtain ⟨-, rfl⟩ := hc'
    exact he'

/-- The value of a fixed monomial in the circuit. -/
def fxV (pt : List FE) (eqv : Nat → FE) (f : FxMon) : FE :=
  FE.ofK f.2.1 * eqv f.1 * powEval (pt.take f.2.2.2.2) (FK.x ^ f.2.2.2.1) * FE.ofK (FK.x ^ f.2.2.1)

/-- **One monomial**: its spec constant is its constant-class part plus its fixed-group part. -/
theorem mono_split (tabs : List Tab) (fix : List (Nat × Nat × Nat × Nat)) (hfix : FixListed tabs fix)
    (hfx : FixExact tabs fix) (pt : List FE) (eqα : List FE) (eqv : Nat → FE) (b : SBlk)
    (hb : b.tab < tabs.length) (m : LMon) (hm : eqv m.1 = eqα.getD m.1 0) :
    eqα.getD m.1 0 * FE.ofK m.2.1 * hT tabs[b.tab]? pt m.2.2 =
      ((if m.2.2 = [] then some (m.1, m.2.1) else none).map fun y => FE.ofK y.2 * eqv y.1).getD 0 +
        ((fxM (tabs.map Tab.shape) fix b m).map (fxV pt eqv)).getD 0 := by
  rcases m with ⟨sl, k, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
  · simp only [hT, if_true, Option.map_some, Option.getD_some, fxM, Option.map_none, Option.getD_none]
    simp only at hm
    rw [hm]; ring
  · have ht : tabs[b.tab]? = some tabs[b.tab] := List.getElem?_eq_getElem hb
    have hSj : (tabs.map Tab.shape).getD b.tab shape0 = tabs[b.tab].shape := by
      rw [List.getD_eq_getElem _ _ (by simpa using hb)]; simp
    have hgd : (tabs[b.tab].shape).cols.getD c none = (tabs[b.tab].cols[c]?).bind colKind := by
      simp [Tab.shape, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases tabs[b.tab].cols[c]? <;> rfl
    simp only [fxM, hSj, comOff, hgd, List.cons_ne_nil, if_false, Option.map_none, Option.getD_none, zero_add]
    rw [ht]
    cases hcs : tabs[b.tab].cols[c]? with
    | none =>
      rw [find_none hfx ht (by intro fn e; rw [hcs]; simp)]
      simp [hT, hcs]
    | some cs =>
      cases cs with
      | com rec off =>
        cases rec
        · simp [hT, hcs, colKind]
        · rw [find_none hfx ht (by intro fn e; rw [hcs]; simp)]
          simp [hT, hcs, colKind]
      | fix fn e =>
        obtain ⟨f, hf, he⟩ := find_some hfix hfx ht hcs
        simp only [hcs, Option.bind_some, colKind, hf, Option.map_some, Option.getD_some, hT, fxV, he]
        simp only at hm ⊢
        rw [hm, Tab.shape]
        ring
  · simp [hT, fxM]

/-- **One block's constant**: the class part and the fixed part. -/
theorem block_split (tabs : List Tab) (fix : List (Nat × Nat × Nat × Nat)) (hfix : FixListed tabs fix)
    (hfx : FixExact tabs fix) (pt eqα : List FE) (eqv : Nat → FE) (β e0 Wb : FE) (b : SBlk) (push : Bool)
    (hb : b.tab < tabs.length) (hm : ∀ m ∈ leafMons b push, eqv m.1 = eqα.getD m.1 0) (he0 : e0 = eqα.getD 0 0) :
    Wb * ((β + eqα.getD 0 0 * FE.ofK b.key.sep) +
        ((leafMons b push).map fun m => eqα.getD m.1 0 * FE.ofK m.2.1 * hT tabs[b.tab]? pt m.2.2).sum) =
      (β + FE.ofK (k0Of b push).1 * e0 + ((k0Of b push).2.map fun m => FE.ofK m.2 * eqv m.1).sum) * Wb +
        Wb * ((fxOf (tabs.map Tab.shape) fix b push).map (fxV pt eqv)).sum := by
  rw [List.map_congr_left fun m hmm => mono_split tabs fix hfix hfx pt eqα eqv b hb m (hm m hmm), List.sum_map_add,
    fxOf_eq, sum_filterMap, k0Of, sum_filterMap, he0]
  ring

theorem sum_zipIdx_fst {α : Type} (l : List α) (F : α → FE) (G : α × Nat → FE) (hG : ∀ x ∈ l.zipIdx, G x = F x.1) :
    (l.zipIdx.map G).sum = (l.map F).sum := by
  rw [List.map_congr_left hG, show (fun x : α × Nat => F x.1) = F ∘ Prod.fst from rfl, ← List.map_map,
    List.zipIdx_map_fst]

/-- **Side `s`'s value from the plan** (push or pull) is `mbValueN`'s. -/
theorem value_circ (tabs : List Tab) (i : BusIn) (fix : List (Nat × Nat × Nat × Nat)) (hfix : FixListed tabs fix)
    (hfx : FixExact tabs fix) {s : Nat} (hs : s < 2) (wv : Nat → FE)
    (hW : ∀ x ∈ (ppS (tabs.map Tab.shape)).zipIdx, wv x.2 = blockWeight i.point x.1.1.κ x.1.2)
    (eqv : Nat → FE)
    (heq : ∀ x ∈ ppS (tabs.map Tab.shape), ∀ m ∈ leafMons x.1 (decide (s = 0)), eqv m.1 = (eqKernel i.alphas).getD m.1 0)
    (e0 : FE) (he0 : e0 = (eqKernel i.alphas).getD 0 0)
    (WS : List Nat → FE) (hWS : ∀ e ∈ (constPlan (tabs.map Tab.shape) fix s).1, WS e.2 = (e.2.map wv).sum)
    (FV : Nat × FK → FE)
    (hFV : ∀ g ∈ (constPlan (tabs.map Tab.shape) fix s).2, FV (g.1.1, g.1.2.1) = FE.ofK g.1.2.1 * eqv g.1.1)
    (PW : Nat × Nat → FE)
    (hPW : ∀ g ∈ (constPlan (tabs.map Tab.shape) fix s).2,
      PW (g.1.2.2.1, g.1.2.2.2) = powEval (i.point.take g.1.2.2.2) (FK.x ^ g.1.2.2.1))
    (GS : List (Nat × Nat) → FE)
    (hGS : ∀ g ∈ (constPlan (tabs.map Tab.shape) fix s).2, GS g.2 = (g.2.map fun m => FE.ofK (FK.x ^ m.2) * wv m.1).sum) :
    i.values.getD s 0 + ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum + 1 +
      ((constPlan (tabs.map Tab.shape) fix s).1.map fun k =>
        (i.beta + FE.ofK k.1.1 * e0 + (k.1.2.map fun m => FE.ofK m.2 * eqv m.1).sum) * WS k.2).sum +
      ((constPlan (tabs.map Tab.shape) fix s).2.map fun g =>
        FV (g.1.1, g.1.2.1) * (PW (g.1.2.2.1, g.1.2.2.2) * GS g.2)).sum =
      mbValueN tabs (busFinalR tabs i) i.point s := by
  set S := tabs.map Tab.shape with hS
  set push := decide (s = 0) with hpush
  set bs := (ppS S).zipIdx.map fun x => (x.1.1, x.2) with hbs
  set key : SBlk × Nat → K0Key := fun x => k0Of x.1 push with hkey
  set fm := bs.flatMap fun x => (fxOf S fix x.1 push).map fun f => (x.2, f) with hfm
  set gk : Nat × FxMon → Nat × FK × Nat × Nat := fun x => (x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2) with hgk
  have hcp : constPlan S fix s =
      ((bs.map key).eraseDups.map fun k => (k, (bs.filter fun x => key x == k).map (·.2)),
       (fm.map gk).eraseDups.map fun g => (g, (fm.filter fun x => gk x == g).map fun x => (x.1, x.2.2.2.1))) := rfl
  rw [hcp] at hWS hFV hPW hGS
  rw [hcp, value_pp tabs i hs]
  simp only [← hS, ← hpush]
  -- the classes
  have h1 : (((bs.map key).eraseDups.map fun k => (k, (bs.filter fun x => key x == k).map (·.2))).map fun k =>
      (i.beta + FE.ofK k.1.1 * e0 + (k.1.2.map fun m => FE.ofK m.2 * eqv m.1).sum) * WS k.2).sum =
      ((ppS S).map fun bo => (i.beta + FE.ofK (k0Of bo.1 push).1 * e0 +
        ((k0Of bo.1 push).2.map fun m => FE.ofK m.2 * eqv m.1).sum) * blockWeight i.point bo.1.κ bo.2).sum := by
    rw [List.map_map]
    rw [List.map_congr_left (g := fun k => ((bs.filter fun x => key x == k).map fun x =>
      (i.beta + FE.ofK (key x).1 * e0 + ((key x).2.map fun m => FE.ofK m.2 * eqv m.1).sum) * wv x.2).sum)
      fun k hk => by
        simp only [Function.comp_apply]
        rw [hWS _ (List.mem_map_of_mem hk), List.map_map, ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
        have : key x = k := beq_iff_eq.mp (List.mem_filter.mp hx).2
        simp only [Function.comp_apply, this]]
    rw [sum_group_eraseDups key, hbs, List.map_map]
    exact sum_zipIdx_fst _ _ _ fun x hx => by simp only [Function.comp_apply, hkey, hW x hx]
  -- the fixed groups
  have h2 : (((fm.map gk).eraseDups.map fun g => (g, (fm.filter fun x => gk x == g).map fun x =>
      (x.1, x.2.2.2.1))).map fun g => FV (g.1.1, g.1.2.1) * (PW (g.1.2.2.1, g.1.2.2.2) * GS g.2)).sum =
      ((ppS S).map fun bo => blockWeight i.point bo.1.κ bo.2 * ((fxOf S fix bo.1 push).map (fxV i.point eqv)).sum).sum := by
    rw [List.map_map]
    rw [List.map_congr_left (g := fun g => ((fm.filter fun x => gk x == g).map fun x =>
      fxV i.point eqv x.2 * wv x.1).sum) fun g hg => by
        have hg' := List.mem_map_of_mem (f := fun g => (g, (fm.filter fun x => gk x == g).map fun x =>
          (x.1, x.2.2.2.1))) hg
        simp only [Function.comp_apply]
        rw [hFV _ hg', hPW _ hg', hGS _ hg', List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
        have : gk x = g := beq_iff_eq.mp (List.mem_filter.mp hx).2
        rw [← this]
        simp only [Function.comp_apply, hgk, fxV]
        ring]
    rw [sum_group_eraseDups gk, hfm, sum_flatMap', hbs, List.map_map]
    refine sum_zipIdx_fst _ _ _ fun x hx => ?_
    simp only [Function.comp_def, List.map_map]
    rw [hW x hx, List.sum_map_mul_right, mul_comm]
  rw [h1, h2]
  have h3 := List.map_congr_left (l := ppS S) fun bo hbo =>
    block_split tabs fix hfix hfx i.point (eqKernel i.alphas) eqv i.beta e0 (blockWeight i.point bo.1.κ bo.2) bo.1 push
      (by simpa [hS] using ppS_tab_lt S bo hbo) (heq bo hbo) he0
  rw [h3, List.sum_map_add]
  ring

/-! ## Assembly -/

theorem mem_colKey {S : List TShape} {s j c : Nat} (hs : s ≠ 2) {x : SBlk × Nat} (hx : x ∈ ppS S)
    (hxj : x.1.tab = j) {m : LMon} (hm : m ∈ leafMons x.1 (decide (s = 0))) (hc : m.2.2 = [c]) :
    ∃ idx, (idx, some (m.1, m.2.1)) ∈ colKey S s j c := by
  obtain ⟨y, hy, rfl⟩ := (exists_zipIdx (ppS S) (· = x)).mpr ⟨x, hx, rfl⟩
  refine ⟨y.2, ?_⟩
  rw [colKey, if_neg hs, List.mem_flatMap]
  refine ⟨(y.1.1, y.2), ?_, ?_⟩
  · simp only [ppOf, List.mem_map, List.mem_filter]
    exact ⟨y, ⟨hy, by simp [hxj]⟩, rfl⟩
  · rw [List.mem_filterMap]
    exact ⟨m, hm, by simp [hc]⟩

theorem atC_left {M : Mem} {z : Cell} (l l2 : List Cell) {k : Nat} (hk : k < l.length) :
    (atC z (l ++ l2) k).val M = (vs M l).getD k 0 := by
  simp [atC, vs, List.getD_eq_getElem?_getD, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

theorem atC_right (z : Cell) (l l2 : List Cell) (k : Nat) : atC z (l ++ l2) (l.length + k) = atC z l2 k := by
  simp [atC, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- `mbLinG`'s slot function. -/
def fOf (z o : Cell) (eb : Nat) (ekP : List (Nat × FK)) (ek : List Cell) : Option (Nat × FK) → Cell :=
  fun x => match x with
    | none => o
    | some y => ekC z eb ekP ek y

/-- `mbLinG`'s scaled-slot plan. -/
def ekPOf (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) : List (Nat × FK) :=
  ekPlan S (((constPlan S fix 0).2 ++ (constPlan S fix 1).2).map fun g => (g.1.1, g.1.2.1))

theorem weights_at {α : Type} {M : Mem} {z : Cell} {L : List α} {W : α → FE} {wpp wc : List Cell}
    (h : vs M wpp = L.map W) : ∀ x ∈ L.zipIdx, (atC z (wpp ++ wc) x.2).val M = W x.1 := by
  intro x hx
  have hl : wpp.length = L.length := by rw [← List.length_map (f := Cell.val M), ← vs, h, List.length_map]
  have hx' := List.mem_zipIdx_iff_getElem?.mp hx
  have hk : x.2 < L.length := (List.getElem?_eq_some_iff.mp hx').1
  rw [atC_left wpp wc (hl ▸ hk), h, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    (List.getElem?_eq_some_iff.mp hx').2]

theorem weights_at_right {α : Type} {M : Mem} {z : Cell} {L : List α} {W : α → FE} {wpp wc : List Cell}
    (h : vs M wc = L.map W) : ∀ x ∈ L.zipIdx, (atC z (wpp ++ wc) (wpp.length + x.2)).val M = W x.1 := by
  intro x hx
  rw [atC_right]
  have := weights_at (z := z) (wc := []) h x hx
  rwa [List.append_nil] at this

/-- **MBL-STMT 7c with RE-FREEZE R3** (H1 `hslot`, H2 `hcnt`, H3 `hfx`): `mbLinG`'s three claims are V_S's. -/
theorem mbLinG_sound' {c : Ctx} {M : Mem} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E)
    (hoE : o.ty = .E) (tabs : List Lvm.M3.Tab) (T : TData) (hsc : Lvm.M3.sumcheckTabs tabs = tabs)
    (hS : T.mbS = tabs.map Lvm.M3.Tab.shape) (hfix : Lvm.Har.FixListed tabs T.mbFix)
    (hlin : Lvm.M3.mbLinB tabs = true) (bc : Lvm.Har.BusC) (i : Lvm.BusIn) (hal : Lvm.Har.vs M bc.al = i.alphas)
    (hbe : bc.be.val M = i.beta) (hpt : Lvm.Har.vs M bc.pt = i.point) (hvals : Lvm.Har.vs M bc.vals = i.values)
    (hal2 : 2 ≤ i.alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E) (hptE : ∀ x ∈ bc.pt, x.ty = .E)
    (hslot : ∀ t ∈ tabs, ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), 3 + k.val.length ≤ 2 ^ i.alphas.length)
    (hcnt : ∀ t ∈ tabs, ∀ r ∈ t.reads, ∀ f e, t.cols[r.2]? ≠ some (Lvm.M3.ColSrc.fix f e))
    (hfx : ∀ f ∈ T.mbFix, ∃ t fn e, tabs[f.1]? = some t ∧ t.cols[f.2.1]? = some (Lvm.M3.ColSrc.fix fn e) ∧
      ∀ r, e r = FE.ofK (FK.x ^ f.2.2.1) * powEval r (FK.x ^ f.2.2.2)) :
    Lvm.Har.SoundG c M (mbLinG z o T bc) fun cs =>
      cs.map (Lvm.Har.CClaim.val M) = (Lvm.M3.mbClaimsN CMain.nu20 tabs i).map fun b => (Com.main, b) := by
  have hfx' : FixExact tabs T.mbFix := hfx
  have hD : bc.pt.length = i.point.length := by rw [← hpt, vs, List.length_map]
  have hpt' : bc.pt.map (Cell.val M) = i.point := hpt
  have hvk : ∀ k, (bc.vals.getD k z).val M = i.values.getD k 0 := fun k => by
    simp only [← hvals, vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bc.vals[k]? <;> simp [hz]
  -- every slot a block's monomial uses is inside the eq table
  have hslotm : ∀ x ∈ ppS (tabs.map Tab.shape), ∀ (push : Bool), ∀ m ∈ leafMons x.1 push,
      m.1 < 2 ^ i.alphas.length := by
    intro x hx push m hm
    obtain ⟨t, ht, hk⟩ := ppS_key tabs hx
    have := hslot t (List.mem_of_getElem? ht) _ hk
    have := slot_lt x.1 push m hm
    omega
  have h4 : 4 ≤ 2 ^ i.alphas.length :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hal2)
  unfold mbLinG
  rw [hS]
  refine soundG_bind (eqTab_sound hz hzE hoE ho halE hal) fun eb heb => ?_
  refine soundG_bind (facG_sound bc.pt) fun facs hfacs => ?_
  have hf1 : (facs.map (·.2)).map (·.val M) = i.point := by rw [hfacs.1, ← hpt]; rfl
  refine soundG_bind (lvlsG_sound hz hzE hoE ho hptE hpt _) fun lt hlt => ?_
  refine soundG_bind (hisG_sound hz ho hf1 hfacs.2 _) fun hi hhi => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wpp hwpp => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wc hwc => ?_
  refine soundG_bind (sumG_sound hz wpp) fun spp hspp => ?_
  refine soundG_bind (sumG_sound hz wc) fun scc hscc => ?_
  have hwpp' : vs M wpp = (ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2 := by
    rw [hwpp, List.map_map]; rfl
  have hwc' : vs M wc = (cS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.2.1 bo.2 := by
    rw [hwc, List.map_map]; rfl
  have hlpp : wpp.length = (ppS (tabs.map Tab.shape)).length := by
    rw [← List.length_map (f := Cell.val M), ← vs, hwpp', List.length_map]
  have hWpp := weights_at (z := z) (wc := wc) hwpp'
  have hWc := weights_at_right (z := z) (wpp := wpp) hwc'
  rw [hlpp] at hWc
  have hsppv : spp.val M = ((ppS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2).sum := by
    rw [hspp, Lvm.Har.sumE_eq_sum, hwpp']
  have hsccv : scc.val M = ((cS (tabs.map Tab.shape)).map fun bo => blockWeight i.point bo.1.2.1 bo.2).sum := by
    rw [hscc, Lvm.Har.sumE_eq_sum, hwc']
  refine soundG_bind (soundG_seqAll (fun x : Nat × FK => lin .E x.2 0 z (ec (eb + x.1)))
    (fun (x : Nat × FK) (r : Cell) => r.val M = FE.ofK x.2 * M.e (eb + x.1)) _
    fun x _ => soundG_mono (soundG_aspec (QB.aspec_lin .E x.2 0 z (ec (eb + x.1)))) fun r hr => by
      rw [hr.1, hz, zero_add, Cell.val_E, ofK_zero, add_zero]) fun ek hek => ?_
  refine soundG_bind (soundG_seqAll (coefG z (wpp ++ wc) (fOf z o eb (ekPOf (tabs.map Tab.shape) T.mbFix) ek))
    (fun (key : CKey) (r : Cell) => r.val M = (key.map fun t => (atC z (wpp ++ wc) t.1).val M *
      (fOf z o eb (ekPOf (tabs.map Tab.shape) T.mbFix) ek t.2).val M).sum) _
    fun key _ => coefG_sound hz (wpp ++ wc) (fOf z o eb (ekPOf (tabs.map Tab.shape) T.mbFix) ek) ho key)
    fun cs hcs => ?_
  refine soundG_bind (soundG_seqAll (fun l : List Nat => sumG z (l.map (atC z (wpp ++ wc))))
    (fun (l : List Nat) (r : Cell) => r.val M = (l.map fun idx => (atC z (wpp ++ wc) idx).val M).sum) _
    fun l _ => soundG_mono (sumG_sound hz _) fun r hr => by rw [hr, Lvm.Har.sumE_eq_sum, vs, List.map_map]; rfl)
    fun ws hws => ?_
  refine soundG_bind (soundG_seqAll (fun x : Nat × Nat => powColG z 0 x.1 (bc.pt.take x.2))
    (fun (x : Nat × Nat) (r : Cell) => r.val M = powEval (i.point.take x.2) (FK.x ^ x.1)) _
    fun x _ => fun p hH _ => by
      dsimp only
      rw [powColG_spec hz 0 x.1 _ p hH, List.map_take, hpt', pow_zero, ofK_one, one_mul]) fun pw hpw => ?_
  refine soundG_bind (soundG_seqAll
    (fun l : List (Nat × Nat) => l.foldlM (fun acc m => lin .E (FK.x ^ m.2) 0 acc (atC z (wpp ++ wc) m.1)) z)
    (fun (l : List (Nat × Nat)) (r : Cell) =>
      r.val M = (l.map fun m => FE.ofK (FK.x ^ m.2) * (atC z (wpp ++ wc) m.1).val M).sum) _
    fun l _ => soundG_mono (soundG_foldlM _ (fun m => FE.ofK (FK.x ^ m.2) * (atC z (wpp ++ wc) m.1).val M) l z
      fun m _ acc => soundG_mono (soundG_aspec (QB.aspec_lin .E (FK.x ^ m.2) 0 acc (atC z (wpp ++ wc) m.1)))
        fun r hr => by rw [hr.1, ofK_zero, add_zero]) fun r hr => by rw [hr, hz, zero_add]) fun gs hgs => ?_
  refine soundG_bind (valG_sound hz bc.be eb spp ws pw gs (wsPlan (tabs.map Tab.shape) T.mbFix)
    (powPlan (tabs.map Tab.shape) T.mbFix) (gsPlan (tabs.map Tab.shape) T.mbFix)
    (fOf z o eb (ekPOf (tabs.map Tab.shape) T.mbFix) ek) (bc.vals.getD 0 z) (constPlan (tabs.map Tab.shape) T.mbFix 0))
    fun v0 hv0 => ?_
  refine soundG_bind (valG_sound hz bc.be eb spp ws pw gs (wsPlan (tabs.map Tab.shape) T.mbFix)
    (powPlan (tabs.map Tab.shape) T.mbFix) (gsPlan (tabs.map Tab.shape) T.mbFix)
    (fOf z o eb (ekPOf (tabs.map Tab.shape) T.mbFix) ek) (bc.vals.getD 1 z) (constPlan (tabs.map Tab.shape) T.mbFix 1))
    fun v1 hv1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 2 z) scc)) fun v2 hv2 => ?_
  refine soundG_pure ?_
  -- the facts the plan lookups give
  set S := tabs.map Tab.shape with hSdef
  set fx := T.mbFix with hfxdef
  set ekP := ekPOf S fx with hekP
  set f := fOf z o eb ekP ek with hfdef
  have heq : ∀ x ∈ ppS S, ∀ (push : Bool), ∀ m ∈ leafMons x.1 push, M.e (eb + m.1) = (eqKernel i.alphas).getD m.1 0 :=
    fun x hx push m hm => heb m.1 (hslotm x hx push m hm)
  have hf : ∀ y : Nat × FK, (y.2 = 1 ∨ y ∈ ekP) → (f (some y)).val M = FE.ofK y.2 * M.e (eb + y.1) :=
    fun y hy => ekC_val eb ekP ek hek y hy
  have hcp : ∀ s < 2, ∀ g ∈ (constPlan S fx s).2, g ∈ (constPlan S fx 0).2 ++ (constPlan S fx 1).2 := by
    intro s hs g hg
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · exact List.mem_append_left _ hg
    · exact List.mem_append_right _ hg
  have hcp1 : ∀ s < 2, ∀ e ∈ (constPlan S fx s).1, e ∈ (constPlan S fx 0).1 ++ (constPlan S fx 1).1 := by
    intro s hs e he
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · exact List.mem_append_left _ he
    · exact List.mem_append_right _ he
  -- the value of side `s < 2`
  have hval : ∀ s < 2, ∀ v : Cell, v.val M = (bc.vals.getD s z).val M + spp.val M + 1 +
      ((constPlan S fx s).1.map fun k => (bc.be.val M + FE.ofK k.1.1 * M.e eb +
        (k.1.2.map fun m => FE.ofK m.2 * M.e (eb + m.1)).sum) * (atC z ws ((wsPlan S fx).idxOf k.2)).val M).sum +
      ((constPlan S fx s).2.map fun g => (f (some (g.1.1, g.1.2.1))).val M *
        ((atC z pw ((powPlan S fx).idxOf (g.1.2.2.1, g.1.2.2.2))).val M *
          (atC z gs ((gsPlan S fx).idxOf g.2)).val M)).sum →
      v.val M = mbValueN tabs (busFinalR tabs i) i.point s := by
    intro s hs v hv
    rw [hv, hvk, hsppv, hbe]
    refine value_circ tabs i fx hfix hfx' hs (fun idx => (atC z (wpp ++ wc) idx).val M) hWpp
      (fun n => M.e (eb + n)) (fun x hx m hm => heq x hx _ m hm) (M.e eb)
      (by rw [← heb 0 (by omega), Nat.add_zero]) (fun l => (atC z ws ((wsPlan S fx).idxOf l)).val M) ?_
      (fun y => (f (some y)).val M) ?_ (fun x => (atC z pw ((powPlan S fx).idxOf x)).val M) ?_
      (fun l => (atC z gs ((gsPlan S fx).idxOf l)).val M) ?_
    · intro e he
      have hm : e.2 ∈ wsPlan S fx := by
        unfold wsPlan; rw [List.mem_eraseDups]; exact List.mem_map_of_mem (hcp1 s hs e he)
      have hi := List.idxOf_lt_length_of_mem hm
      have := f2_getD hws z _ hi
      rw [List.getElem_idxOf hi] at this
      exact this
    · intro g hg
      refine hf _ ?_
      by_cases h1 : g.1.2.1 = 1
      · exact Or.inl h1
      · exact Or.inr (List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_append_right _
          (List.mem_map.mpr ⟨g, hcp s hs g hg, rfl⟩)), by simpa using h1⟩)
    · intro g hg
      have hm : (g.1.2.2.1, g.1.2.2.2) ∈ powPlan S fx := by
        unfold powPlan; rw [List.mem_eraseDups]; exact List.mem_map_of_mem (f := fun g : FxKey => (g.1.2.2.1, g.1.2.2.2)) (hcp s hs g hg)
      have hi := List.idxOf_lt_length_of_mem hm
      have := f2_getD hpw z _ hi
      rw [List.getElem_idxOf hi] at this
      exact this
    · intro g hg
      have hm : g.2 ∈ gsPlan S fx := by
        unfold gsPlan; rw [List.mem_eraseDups]; exact List.mem_map_of_mem (hcp s hs g hg)
      have hi := List.idxOf_lt_length_of_mem hm
      have := f2_getD hgs z _ hi
      rw [List.getElem_idxOf hi] at this
      exact this
  -- the coefficients
  have hcv : ∀ s < 3, ∀ x ∈ partsPlan S s,
      (atC z cs ((keysPlan S).idxOf x.2.2)).val M = coefN (formN (busFinalR tabs i) x.1 s) x.2.1 := by
    intro s hs x hx
    obtain ⟨hj, hkey⟩ := mem_partsPlan hx
    have hj' : x.1 < tabs.length := by simpa [hSdef] using hj
    have hkP : x.2.2 ∈ keysPlan S := by
      unfold keysPlan; rw [List.mem_eraseDups]
      exact List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, List.mem_map_of_mem hx⟩
    have hi := List.idxOf_lt_length_of_mem hkP
    have hc := f2_getD hcs z _ hi
    rw [List.getElem_idxOf hi] at hc
    rw [show atC z cs ((keysPlan S).idxOf x.2.2) = cs.getD ((keysPlan S).idxOf x.2.2) z from rfl, hc]
    by_cases h2 : s = 2
    · subst h2
      rw [hkey]
      exact colKey_val_cnt tabs i hj' x.2.1 (fun idx => (atC z (wpp ++ wc) idx).val M) hWc
        (fun y => (f y).val M) ho
    · rw [hkey]
      refine colKey_val_pp tabs i (by omega) hj' x.2.1 (fun idx => (atC z (wpp ++ wc) idx).val M) hWpp
        (fun y => (f y).val M) ?_
      intro y hy hyj m hm hmc
      show (f (some (m.1, m.2.1))).val M = _
      rw [hf _ ?_, heq y hy _ m hm]
      by_cases h1 : m.2.1 = 1
      · exact Or.inl h1
      · obtain ⟨idx, hidx⟩ := mem_colKey h2 hy hyj hm hmc
        exact Or.inr (List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨x.2.2, hkP, by rw [hkey]; exact List.mem_filterMap.mpr ⟨_, hidx, rfl⟩⟩)),
          by simpa using h1⟩)
  simp only [List.map_cons, List.map_nil, mbClaimsN, show List.range 3 = [0, 1, 2] from rfl, CClaim.val]
  refine List.cons_eq_cons.mpr ⟨Prod.ext rfl ?_, List.cons_eq_cons.mpr ⟨Prod.ext rfl ?_,
    List.cons_eq_cons.mpr ⟨Prod.ext rfl ?_, rfl⟩⟩⟩
  · refine congrArg₂ (sumClaim CMain.nu20) ?_ (hval 0 (by norm_num) v0 hv0)
    rw [List.map_map, ← parts_eq tabs i hlin (s := 0) (by norm_num)
      (fun key => (atC z cs ((keysPlan S).idxOf key)).val M) (hcv 0 (by norm_num))]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, vs, List.map_take, hpt']
    rfl
  · refine congrArg₂ (sumClaim CMain.nu20) ?_ (hval 1 (by norm_num) v1 hv1)
    rw [List.map_map, ← parts_eq tabs i hlin (s := 1) (by norm_num)
      (fun key => (atC z cs ((keysPlan S).idxOf key)).val M) (hcv 1 (by norm_num))]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, vs, List.map_take, hpt']
    rfl
  · refine congrArg₂ (sumClaim CMain.nu20) ?_ ?_
    · rw [List.map_map, ← parts_eq tabs i hlin (s := 2) (by norm_num)
        (fun key => (atC z cs ((keysPlan S).idxOf key)).val M) (hcv 2 (by norm_num))]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, vs, List.map_take, hpt']
      rfl
    · rw [hv2.1, hvk, hsccv, value_cnt tabs i hcnt, ofK_one, one_mul]
      ring

/-! ## RE-FREEZE R3's hypotheses at the mini-bus tables (`mbT`, `mbFixOf`): structural, no table-wise decide -/

/-- Every key of the mini-bus tables has one value limb (seed arrays: one `K` limb; reads: `readKey`). -/
theorem mbT_keys (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    ∀ t ∈ mbT C wordK fin cnt, ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), k.val.length = 1 := by
  intro t ht k hk
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    have hv : a.val.length = 1 := by
      simp only [mbArrs, List.mem_map] at ha
      obtain ⟨x, -, rfl⟩ := ha
      rfl
    simp only [InArr.tab, List.map_nil, List.nil_append, List.map_cons, List.mem_singleton] at hk
    subst hk
    simp [hv]
  · simp only [capReads, List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    simp only [readTab, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hk
    subst hk
    rfl

/-- **R3 H1 at the mini-bus tables**: with at least two batching challenges every slot is in the eq table. -/
theorem mbT_slots (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) {n : Nat} (hn : 2 ≤ n) :
    ∀ t ∈ mbT C wordK fin cnt, ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), 3 + k.val.length ≤ 2 ^ n := by
  intro t ht k hk
  rw [mbT_keys C wordK fin cnt t ht k hk]
  exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)

/-- **R3 H2 at the mini-bus tables**: the reads' count columns are committed. -/
theorem mbT_cnt (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    ∀ t ∈ mbT C wordK fin cnt, ∀ r ∈ t.reads, ∀ f e, t.cols[r.2]? ≠ some (ColSrc.fix f e) := by
  intro t ht r hr f e
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
    simp [InArr.tab] at hr
  · simp only [capReads, List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    simp only [readTab, List.mem_singleton] at hr
    subst hr
    show [ColSrc.com false _, ColSrc.com false _, ColSrc.com false _][2]? ≠ _
    simp

/-- **R3 H3 at the mini-bus tables**: every `mbFixOf` entry names a seed array's address column, whose closed form
is its power form (at any finalize placements). -/
theorem mbFixOf_exact (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    ∀ f ∈ mbFixOf C, ∃ t fn e, (mbT C wordK fin cnt)[f.1]? = some t ∧ t.cols[f.2.1]? = some (ColSrc.fix fn e) ∧
      ∀ r, e r = FE.ofK (FK.x ^ f.2.2.1) * powEval r (FK.x ^ f.2.2.2) := by
  intro f hf
  simp only [mbFixOf, List.mem_map] at hf
  obtain ⟨⟨a, k⟩, hak, rfl⟩ := hf
  rw [List.mem_zipIdx_iff_getElem?, mbArrs_get] at hak
  cases hb : (mbBlocks C.p)[k]? with
  | none => simp [hb] at hak
  | some q =>
    simp only [hb, Option.map_some, Option.some.injEq] at hak
    subst hak
    have hk : k < (mbBlocks C.p).length := (List.getElem?_eq_some_iff.mp hb).1
    have hlen : ((mbArrs C fin).map InArr.tab).length = (mbBlocks C.p).length := by simp [mbArrs]
    refine ⟨InArr.tab ⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], fin k, none⟩,
      fun x => FK.x ^ ((lay C).sb + 17 * q.2 + q.1 + 17 * x),
      fun r => FE.ofK (FK.x ^ ((lay C).sb + 17 * q.2 + q.1)) * powEval r (FK.x ^ 17), ?_, rfl, fun r => rfl⟩
    rw [mbT, List.getElem?_append_left (by rw [hlen]; exact hk), List.getElem?_map, mbArrs_get, hb]
    rfl

end Lvm.E2Q
