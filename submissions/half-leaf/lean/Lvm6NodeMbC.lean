-- New for lvm6 (WP MBT, phase 2). The mini-bus claims' real inputs: a gadget `mbPreG tabs o` that computes, from
-- the mini-bus walk's output cells `o` (`α`, `β`, `ζ`, the three values), the parts (coefficient cell, block,
-- point cells) and the value cell of each of the three sum claims `mbClaimsG`, for any list of tables; and its HAR.
import Lvm6NodeMbS

/-!
# The mini-bus claims' parts and values as cells (`mbPreG`, WP MBT phase 2)

`mbClaimsG ν tabs b` (`Lvm6MbProg`) is, per side `s` (push, pull, count), `sumClaimG ν (mbPartsG tabs r s)
(mbValueG tabs r s)` with `r = busResG tabs b`. Its weights are cell computations of `b`; `mbPreG` mirrors the
definitions step by step, generic over the tables (the shapes are static, the values are cells):

* `eqsG`: `eqKernelF α` (`eqAtG` per index); `leafC`, `sideBlocksC`: `leafFormG`, `sideBlocksG` with cell
  coefficients; `sideWG`: `stackBlocksG` (`stk` on the stable sort by `κ`, the same as the spec's) with the weights
  `eqAboveG ⟨κ, off⟩ ζ` (`eqAtG` on `ζ.drop κ`); `bucketC`: `bucketG`; `totC`: the side totals;
* `partsC`: `mbPartsG` (`coefC` = `coefG`); `valC`: `mbValueG` (`constC` = `constG`, the fixed columns' `mleFixG`
  from `eq` tables of `ζ.take τ`, one per `τ`).

**`hs_mbPreG`** (the HAR): where `mbPreG`'s rows hold, its parts are `mbPartsG tabs r s` (`partsV`) and its values
`mbValueG tabs r s`, `r = busFinalG tabs α β ζ v` at the cells' values: what `mbClaim_ok` takes for claims 50–52.
Every statement is for every `tabs`; nothing is evaluated.
-/

set_option autoImplicit false

namespace Lvm6.Node.MbC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK Lvm6.QC Lvm.M3 Lvm6.Mb Lvm6.Node.MbS

variable {c : Ctx} {M : Mem}

/-! ## Cell forms and blocks -/

/-- A form with cell coefficients. -/
abbrev FormC := List (List ℕ × C2)

/-- Its value. -/
def evF (M : Mem) (f : FormC) : FormG := ⟨f.map fun t ↦ (t.1, ev2 M t.2)⟩

/-- A bus block with a cell form. -/
structure VBlockC where
  tab : ℕ
  κ : ℕ
  form : FormC

/-- Its value. -/
def evB (M : Mem) (b : VBlockC) : VBlockG := ⟨b.tab, b.κ, evF M b.form⟩

/-- A weighted block's value. -/
def evBW (M : Mem) (bw : VBlockC × C2) : VBlockG × E2 := (evB M bw.1, ev2 M bw.2)

/-- One part's value (`partsV`'s element). -/
def evP (M : Mem) (q : C2 × LeanVM.Protocol.Verifier.Placement × List C2) : E2 × LeanVM.Protocol.Verifier.Placement × List E2 :=
  (ev2 M q.1, q.2.1, q.2.2.map (ev2 M))

theorem getD_ev2 {l : List C2} {L : List E2} (h : l.map (ev2 M) = L) {z : C2} (hz : ev2 M z = 0) (i : ℕ) :
    ev2 M (l.getD i z) = L.getD i 0 := by
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hz]

theorem evF_nil : evF M [] = default := rfl

theorem evF_append (f g : FormC) : evF M (f ++ g) = ⟨(evF M f).terms ++ (evF M g).terms⟩ := by
  simp [evF]

theorem evF_flatten (L : List FormC) : evF M L.flatten = ⟨(L.map (evF M)).flatMap (·.terms)⟩ := by
  simp [evF, List.map_flatten, List.flatMap, List.map_map, Function.comp_def]

/-! ## Sums -/

/-- `acc + Σ l`. -/
def sumFrom : C2 → List C2 → BM C2
  | acc, [] => pure acc
  | acc, x :: xs => g2Add acc x >>= fun a ↦ sumFrom a xs

theorem hs_sumFrom : ∀ (l : List C2) (acc : C2),
    Hs c M (sumFrom acc l) fun r ↦ ev2 M r = ev2 M acc + (l.map (ev2 M)).sum
  | [], acc => hs_pure (by simp)
  | x :: xs, acc => hs_bind (hs_g2Add acc x) fun a ha ↦ hs_mono (hs_sumFrom xs a) fun r hr ↦ by
      rw [hr, ev2_add ha, List.map_cons, List.sum_cons, add_assoc]

/-- `Σ l` (the zero cell `z` for `[]`; from the first element otherwise). -/
def sumG (z : C2) : List C2 → BM C2
  | [] => pure z
  | x :: xs => sumFrom x xs

theorem hs_sumG {z : C2} (hz : z.val M = 0) (l : List C2) :
    Hs c M (sumG z l) fun r ↦ ev2 M r = sumF (l.map (ev2 M)) := by
  cases l with
  | nil => exact hs_pure (by rw [ev2_of_zero hz]; rfl)
  | cons x xs => exact hs_mono (hs_sumFrom xs x) fun r hr ↦ by rw [hr, sumF_eq_sum, List.map_cons, List.sum_cons]

/-- Dropping the zero cell does not change a sum. -/
theorem sum_filter_ne {z : C2} (hz : ev2 M z = 0) :
    ∀ l : List C2, ((l.filter (· != z)).map (ev2 M)).sum = (l.map (ev2 M)).sum
  | [] => rfl
  | x :: l => by
    by_cases h : x = z
    · subst h
      simp [List.filter_cons, hz, sum_filter_ne hz l]
    · simp [List.filter_cons, h, sum_filter_ne hz l]

/-- `Σ l` over the cells other than `z`. -/
def sumNZ (z : C2) (l : List C2) : BM C2 := sumG z (l.filter (· != z))

theorem hs_sumNZ {z : C2} (hz : z.val M = 0) (l : List C2) :
    Hs c M (sumNZ z l) fun r ↦ ev2 M r = sumF (l.map (ev2 M)) :=
  hs_mono (hs_sumG hz _) fun r hr ↦ by rw [hr, sumF_eq_sum, sumF_eq_sum, sum_filter_ne (ev2_of_zero hz)]

/-! ## `eqKernelF α` -/

theorem eqKernelF_eq_map (a : List E2) : eqKernelF a = (List.range (2 ^ a.length)).map (eqAtF a) := by
  apply List.ext_getElem
  · simp [Lvm6.eqKernelF_length]
  · intro i h1 h2
    have h := Lvm6.eqKernelF_getD a i
    rw [List.getD_eq_getElem _ _ h1, if_pos (by simpa [Lvm6.eqKernelF_length] using h1)] at h
    rw [h, List.getElem_map, List.getElem_range]

/-- The equality weights of `α` (`eqKernelF`), by the trie (`eqTabG`). -/
def eqsG (z one : C2) (al : List C2) : BM (List C2) := onesG al >>= fun os ↦ eqTabG z one al os

theorem hs_eqsG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (al : List C2) :
    Hs c M (eqsG z one al) fun e ↦ e.map (ev2 M) = eqKernelF (al.map (ev2 M)) :=
  hs_bind (hs_onesG al z) fun _ hos ↦ hs_mono (hs_eqTabG hz hone hos) fun e he ↦ by
    rw [he, eqKernelF_eq_map, List.length_map]

/-! ## Leaf forms -/

theorem ev2_ofK {k : C2} (a : FK) (h : k.val M = FE2.ofK a) : ev2 M k = kG a := by
  simp [ev2, h, kG]

theorem kG_one' : kG 1 = 1 := by
  show FE2.toE2 (FE2.ofK 1) = 1
  rw [show FE2.ofK 1 = 1 from rfl]
  simp

/-- `a + k·b` (`g2Lin k 0`). -/
theorem ev2_lin0 {r a b : C2} {k : FK} (h : r.val M = a.val M + FE2.ofK k * b.val M + 0) :
    ev2 M r = ev2 M a + kG k * ev2 M b := by
  simp only [ev2, h, add_zero, FE2.toE2_add, FE2.fe2_mul_eq, kG]

/-- `w·k` for a constant `k`: `w` itself for `k = 1`, else one row pair (`g2Lin k 0 z w`). -/
def kMulC (z w : C2) (k : FK) : BM C2 := if k == 1 then pure w else g2Lin k 0 z w

theorem hs_kMulC {z : C2} (hz : z.val M = 0) (w : C2) (k : FK) :
    Hs c M (kMulC z w k) fun r ↦ ev2 M r = ev2 M w * kG k := by
  unfold kMulC
  split_ifs with h
  · exact hs_pure (by rw [beq_iff_eq.mp h, kG_one', mul_one])
  · exact hs_mono (hs_g2Lin k 0 z w) fun r hr ↦ by rw [ev2_lin0 hr, ev2_of_zero hz, zero_add, mul_comm]

/-- `cpolyFormG w P` with cell coefficients. -/
def cpolyC (z w : C2) (P : CPoly) : BM FormC :=
  mapB (fun m : FK × List ℕ ↦ kMulC z w m.1 >>= fun r ↦ pure (m.2, r)) P

theorem hs_cpolyC {z : C2} (hz : z.val M = 0) (w : C2) (P : CPoly) :
    Hs c M (cpolyC z w P) fun f ↦ evF M f = cpolyFormG (ev2 M w) P :=
  hs_mono (hs_mapB2 _ (fun m : FK × List ℕ ↦ (m.2, ev2 M w * kG m.1)) (fun t : List ℕ × C2 ↦ (t.1, ev2 M t.2))
    (fun m ↦ hs_bind (hs_kMulC hz w m.1) fun r hr ↦ hs_pure (by rw [hr])) P) fun f hf ↦ by
    simp only [evF, cpolyFormG, hf]

/-- `leafFormG eqα β k cnt` with cell coefficients (`e` the cells of `eqα`; `c0` a shared constant term
`β + eqα₀·sep₀`, used when `k.sep = sep₀`). -/
def leafC (z : C2) (e : List C2) (be : C2) (c0s : FK × C2) (k : Key) (cnt : CPoly) : BM FormC :=
  (if k.sep == c0s.1 then pure c0s.2 else g2Lin k.sep 0 be (e.getD 0 z)) >>= fun c0 ↦
  cpolyC z (e.getD 1 z) k.addr >>= fun A ↦ cpolyC z (e.getD 2 z) cnt >>= fun C ↦
  mapB (fun x : CPoly × ℕ ↦ cpolyC z (e.getD (3 + x.2) z) x.1) k.val.zipIdx >>= fun V ↦
  pure ([([], c0)] ++ A ++ C ++ V.flatten)

theorem hs_leafC {z : C2} (hz : z.val M = 0) {e : List C2} {eqα : List E2}
    (he : ∀ i, ev2 M (e.getD i z) = eqα.getD i 0) (be : C2) {c0s : FK × C2}
    (hc0s : ev2 M c0s.2 = ev2 M be + eqα.getD 0 0 * kG c0s.1) (k : Key) (cnt : CPoly) :
    Hs c M (leafC z e be c0s k cnt) fun f ↦ evF M f = leafFormG eqα (ev2 M be) k cnt := by
  have hc : Hs c M (if k.sep == c0s.1 then pure c0s.2 else g2Lin k.sep 0 be (e.getD 0 z)) fun c0 ↦
      ev2 M c0 = ev2 M be + eqα.getD 0 0 * kG k.sep := by
    split_ifs with h
    · exact hs_pure (by rw [hc0s, beq_iff_eq.mp h])
    · exact hs_mono (hs_g2Lin _ _ _ _) fun r hr ↦ by rw [ev2_lin0 hr, he, mul_comm]
  refine hs_bind hc fun c0 h0 ↦
    hs_bind (hs_cpolyC hz _ _) fun A hA ↦ hs_bind (hs_cpolyC hz _ _) fun C hC ↦
    hs_bind (hs_mapB2 _ (fun x : CPoly × ℕ ↦ cpolyFormG (eqα.getD (3 + x.2) 0) x.1) (evF M)
      (fun x ↦ hs_mono (hs_cpolyC hz _ _) fun f hf ↦ by rw [hf, he]) _) fun V hV ↦ hs_pure ?_
  rw [he] at hA hC
  simp only [leafFormG, formSumG, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
  rw [evF_append, evF_append, evF_append, evF_flatten, hV, hA, hC]
  simp [evF, h0, List.flatMap_map]

/-! ## The sides' blocks -/

/-- The first key's separator (the shared constant term's). -/
def sep0 (tabs : List Tab) : FK :=
  ((tabs.flatMap fun t ↦ t.reads.map (·.1) ++ t.seeds.map (·.1)).head?.map (·.sep)).getD 0

/-- `sideBlocksG tabs eqα β` with cell forms (`one` the count blocks' coefficient). -/
def sideBlocksC (z one : C2) (e : List C2) (be : C2) (tabs : List Tab) : BM (List (List VBlockC)) :=
  g2Lin (sep0 tabs) 0 be (e.getD 0 z) >>= fun c0 ↦
  mapB (fun x : Tab × ℕ ↦
    mapB (fun r : Key × ℕ ↦ leafC z e be (sep0 tabs, c0) r.1 [(FK.x, [r.2])] >>= fun f ↦ pure (⟨x.2, x.1.τ, f⟩ : VBlockC))
      x.1.reads >>= fun R ↦
    mapB (fun s : Key × ℕ ↦ leafC z e be (sep0 tabs, c0) s.1 (CPoly.const 1) >>= fun f ↦ pure (⟨x.2, x.1.τ, f⟩ : VBlockC))
      x.1.seeds >>= fun S ↦ pure (R ++ S)) tabs.zipIdx >>= fun P ↦
  mapB (fun x : Tab × ℕ ↦
    mapB (fun r : Key × ℕ ↦ leafC z e be (sep0 tabs, c0) r.1 (CPoly.var r.2) >>= fun f ↦ pure (⟨x.2, x.1.τ, f⟩ : VBlockC))
      x.1.reads >>= fun R ↦
    mapB (fun s : Key × ℕ ↦ leafC z e be (sep0 tabs, c0) s.1 (CPoly.var s.2) >>= fun f ↦ pure (⟨x.2, x.1.τ, f⟩ : VBlockC))
      x.1.seeds >>= fun S ↦ pure (R ++ S)) tabs.zipIdx >>= fun Q ↦
  pure [P.flatten, Q.flatten,
    tabs.zipIdx.flatMap fun x ↦ x.1.counts.map fun cc ↦ (⟨x.2, x.1.τ, [([cc.val], one)]⟩ : VBlockC)]

theorem hs_blocks {z : C2} (hz : z.val M = 0) {e : List C2} {eqα : List E2}
    (he : ∀ i, ev2 M (e.getD i z) = eqα.getD i 0) (be : C2) {c0s : FK × C2}
    (hc0s : ev2 M c0s.2 = ev2 M be + eqα.getD 0 0 * kG c0s.1) (cn : Key × ℕ → CPoly) (j τ : ℕ)
    (l : List (Key × ℕ)) :
    Hs c M (mapB (fun r : Key × ℕ ↦ leafC z e be c0s r.1 (cn r) >>= fun f ↦ pure (⟨j, τ, f⟩ : VBlockC)) l)
      fun R ↦ R.map (evB M) = l.map fun r ↦ (⟨j, τ, leafFormG eqα (ev2 M be) r.1 (cn r)⟩ : VBlockG) :=
  hs_mapB2 _ (fun r : Key × ℕ ↦ (⟨j, τ, leafFormG eqα (ev2 M be) r.1 (cn r)⟩ : VBlockG)) (evB M)
    (fun r ↦ hs_bind (hs_leafC hz he be hc0s r.1 (cn r)) fun f hf ↦ hs_pure (by
      show (⟨j, τ, evF M f⟩ : VBlockG) = _
      rw [hf])) l

theorem hs_sideBlocksC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {e : List C2} {eqα : List E2}
    (he : ∀ i, ev2 M (e.getD i z) = eqα.getD i 0) (be : C2) (tabs : List Tab) :
    Hs c M (sideBlocksC z one e be tabs) fun bl ↦ bl.map (·.map (evB M)) = sideBlocksG tabs eqα (ev2 M be) := by
  refine hs_bind (hs_g2Lin _ _ _ _) fun c0 hc0 ↦ ?_
  have hc0s : ev2 M (sep0 tabs, c0).2 = ev2 M be + eqα.getD 0 0 * kG (sep0 tabs, c0).1 := by
    rw [ev2_lin0 hc0, he, mul_comm]
  refine hs_bind (hs_mapB2 _ (fun x : Tab × ℕ ↦ x.1.reads.map (fun r ↦ (⟨x.2, x.1.τ,
      leafFormG eqα (ev2 M be) r.1 [(FK.x, [r.2])]⟩ : VBlockG)) ++ x.1.seeds.map (fun s ↦ (⟨x.2, x.1.τ,
      leafFormG eqα (ev2 M be) s.1 (CPoly.const 1)⟩ : VBlockG))) (·.map (evB M))
    (fun x ↦ hs_bind (hs_blocks hz he be hc0s (fun r ↦ [(FK.x, [r.2])]) x.2 x.1.τ x.1.reads) fun R hR ↦
      hs_bind (hs_blocks hz he be hc0s (fun _ ↦ CPoly.const 1) x.2 x.1.τ x.1.seeds) fun S hS ↦
        hs_pure (by rw [List.map_append, hR, hS])) _) fun P hP ↦ ?_
  refine hs_bind (hs_mapB2 _ (fun x : Tab × ℕ ↦ x.1.reads.map (fun r ↦ (⟨x.2, x.1.τ,
      leafFormG eqα (ev2 M be) r.1 (CPoly.var r.2)⟩ : VBlockG)) ++ x.1.seeds.map (fun s ↦ (⟨x.2, x.1.τ,
      leafFormG eqα (ev2 M be) s.1 (CPoly.var s.2)⟩ : VBlockG))) (·.map (evB M))
    (fun x ↦ hs_bind (hs_blocks hz he be hc0s (fun r ↦ CPoly.var r.2) x.2 x.1.τ x.1.reads) fun R hR ↦
      hs_bind (hs_blocks hz he be hc0s (fun s ↦ CPoly.var s.2) x.2 x.1.τ x.1.seeds) fun S hS ↦
        hs_pure (by rw [List.map_append, hR, hS])) _) fun Q hQ ↦ hs_pure ?_
  simp only [sideBlocksG, List.map_cons, List.map_nil, List.map_flatten, hP, hQ, List.flatMap,
    List.map_flatMap, List.map_map, Function.comp_def]
  simp [evB, evF, hone]

/-! ## Stacking and weights -/

theorem stk_map {X Y : Type} (κx : X → ℕ) (κy : Y → ℕ) (f : X → Y) (hf : ∀ x, κy (f x) = κx x) :
    ∀ (l : List X) (o : ℕ), stk κy (l.map f) o = (stk κx l o).map (Prod.map f id)
  | [], _ => rfl
  | x :: l, o => by simp [stk, hf, stk_map κx κy f hf l]

/-- The blocks sorted largest first (stable; `sortG`'s order). -/
def sortC (bs : List VBlockC) : List VBlockC := bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)

theorem sortG_map (bs : List VBlockC) : sortG (bs.map (evB M)) = (sortC bs).map (evB M) := by
  unfold sortG sortC
  exact (List.map_mergeSort (r := fun a b : VBlockC ↦ decide (b.κ ≤ a.κ))
    (s := fun a b : VBlockG ↦ decide (b.κ ≤ a.κ)) (f := evB M) (fun _ _ _ _ ↦ rfl)).symm

theorem stackBlocksG_map (bs : List VBlockC) :
    stackBlocksG (bs.map (evB M)) = (stk VBlockC.κ (sortC bs) 0).map (Prod.map (evB M) id) := by
  rw [stackBlocksG_eq, sortG_map]
  exact stk_map VBlockC.κ VBlockG.κ (evB M) (fun _ ↦ rfl) _ 0

theorem zip_map_ev {X : Type} (f : X → VBlockC) (g : X → E2) :
    ∀ (S : List X) (W : List C2), W.map (ev2 M) = S.map g →
      ((S.map f).zip W).map (evBW M) = S.map fun x ↦ (evB M (f x), g x)
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: S, w :: W, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, zip_map_ev f g S W h.2, evBW, h.1]

/-- A side's stacked blocks with their weights `eqAboveG ⟨κ, off⟩ ζ`, from the trie of the blocks (`eqHiG`; `os`
the cells `1 + ζ`). -/
def sideWG (z one : C2) (pt os : List C2) (bs : List VBlockC) : BM (List (VBlockC × C2)) :=
  eqHiG z one pt os ((stk VBlockC.κ (sortC bs) 0).map fun bo ↦ (bo.1.κ, bo.2 / 2 ^ bo.1.κ)) >>= fun W ↦
    pure (((stk VBlockC.κ (sortC bs) 0).map (·.1)).zip W)

theorem hs_sideWG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2) {os : List C2}
    (hos : OnesOk M z pt os) (bs : List VBlockC) :
    Hs c M (sideWG z one pt os bs) fun sd ↦ sd.map (evBW M) =
      (stackBlocksG (bs.map (evB M))).map fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ (pt.map (ev2 M))) := by
  refine hs_bind (hs_eqHiG hz hone hos _) fun W hW ↦ hs_pure ?_
  rw [List.map_map] at hW
  rw [zip_map_ev _ _ _ W hW, stackBlocksG_map, List.map_map]
  refine List.map_congr_left fun bo _ ↦ ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, eqAboveG_eq]
  rfl

/-! ## Buckets and totals -/

/-- `w·a` (`w` itself when `a` is the cell `one`). -/
def mulC (z one w a : C2) : BM C2 := if a = one then pure w else g2Mul w a z

theorem hs_mulC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (w a : C2) :
    Hs c M (mulC z one w a) fun r ↦ ev2 M r = ev2 M w * ev2 M a := by
  unfold mulC
  split_ifs with h
  · exact hs_pure (by rw [h, hone, mul_one])
  · exact hs_mono (hs_g2Mul w a z) fun r hr ↦ by rw [ev2_mul hr, ev2_of_zero hz, add_zero]

/-- `bucketG s j` with cell coefficients. -/
def bucketC (z one : C2) (s : List (VBlockC × C2)) (j : ℕ) : BM FormC :=
  mapB (fun bw : VBlockC × C2 ↦ mapB (fun t : List ℕ × C2 ↦ mulC z one bw.2 t.2 >>= fun r ↦ pure (t.1, r))
    bw.1.form) ((s.filter fun bw ↦ bw.1.tab == j).reverse) >>= fun L ↦ pure L.flatten

theorem hs_bucketC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (s : List (VBlockC × C2)) (j : ℕ) :
    Hs c M (bucketC z one s j) fun f ↦ evF M f = ⟨bucketG (s.map (evBW M)) j⟩ := by
  refine hs_bind (hs_mapB2 _ (fun bw : VBlockC × C2 ↦ (⟨(evF M bw.1.form).terms.map fun t ↦
      (t.1, ev2 M bw.2 * t.2)⟩ : FormG)) (evF M) (fun bw ↦ hs_mono (hs_mapB2 _
      (fun t : List ℕ × C2 ↦ (t.1, ev2 M bw.2 * ev2 M t.2)) (fun t : List ℕ × C2 ↦ (t.1, ev2 M t.2))
      (fun t ↦ hs_bind (hs_mulC hz hone _ _) fun r hr ↦ hs_pure (by rw [hr])) _) fun f hf ↦ by
      simp only [evF, hf, List.map_map, Function.comp_def]) _) fun L hL ↦ hs_pure ?_
  rw [evF_flatten, hL]
  simp only [bucketG, List.filter_map, List.map_reverse, Function.comp_def, evBW, evB]
  simp [evF, evBW, evB, List.flatMap, Function.comp_def]

/-- Side `k`'s total `v_k + 1 + Σ_b w_b`. -/
def totC (z one : C2) (sd : List (List (VBlockC × C2))) (vs : List C2) (k : ℕ) : BM C2 :=
  sumG z ((sd.getD k []).map (·.2)) >>= fun sw ↦ g2Add (vs.getD k z) one >>= fun a ↦ g2Add a sw

theorem hs_totC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {sd : List (List (VBlockC × C2))}
    {sides : List (List (VBlockG × E2))} (hsd : sd.map (·.map (evBW M)) = sides) (vs : List C2) (k : ℕ) :
    Hs c M (totC z one sd vs k) fun r ↦
      ev2 M r = (vs.map (ev2 M)).getD k 0 + 1 + sumF ((sides.getD k []).map (·.2)) := by
  refine hs_bind (hs_sumG hz _) fun sw hsw ↦ hs_bind (hs_g2Add _ one) fun a ha ↦ hs_mono (hs_g2Add a sw)
    fun r hr ↦ ?_
  rw [ev2_add hr, ev2_add ha, getD_ev2 rfl (ev2_of_zero hz), hone, hsw, ← hsd]
  congr 2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases sd[k]? <;> simp [evBW]

/-! ## Parts and values -/

/-- `coefG f c` with cell coefficients. -/
def coefC (z : C2) (f : FormC) (cc : ℕ) : BM C2 := sumG z ((f.filter fun m ↦ m.1 == [cc]).map (·.2))

theorem hs_coefC {z : C2} (hz : z.val M = 0) (f : FormC) (cc : ℕ) :
    Hs c M (coefC z f cc) fun r ↦ ev2 M r = Mb.coefG (evF M f) cc :=
  hs_mono (hs_sumG hz _) fun r hr ↦ by
    rw [hr]
    unfold Mb.coefG evF
    simp only [List.filter_map, List.map_map, Function.comp_def]

/-- The cell form of table `j` on side `s` (`formG`'s lookup). -/
def formAt (forms : List (List FormC)) (j s : ℕ) : FormC := (forms.getD j []).getD s []

theorem formG_evR (forms : List (List FormC)) (pt : List E2) (tot : List E2) (j s : ℕ) :
    formG ⟨pt, forms.map (·.map (evF M)), tot⟩ j s = evF M (formAt forms j s) := by
  simp only [formG, formAt, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases forms[j]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
  · rfl
  · rename_i l
    rw [List.getElem?_map]
    cases l[s]? <;> rfl

theorem map_filterMap_id {α β : Type} (g : α → β) :
    ∀ l : List (Option α), (l.filterMap id).map g = (l.map (Option.map g)).filterMap id
  | l => by rw [List.map_filterMap, List.filterMap_map]; rfl

theorem filterMap_id_map {α β : Type} (F : α → Option β) :
    ∀ l : List α, (l.map F).filterMap id = l.filterMap F
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, filterMap_id_map F l]
    rfl

/-- `mbPartsG tabs r s` with cell coefficients and points. -/
def partsC (z : C2) (tabs : List Tab) (forms : List (List FormC)) (pt : List C2) (s : ℕ) :
    BM (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) :=
  mapB (fun x : Tab × ℕ ↦ mapB (fun cc ↦ match x.1.cols[cc]? with
      | some (ColSrc.com _ off) => coefC z (formAt forms x.2 s) cc >>= fun k ↦
          pure (some (k, (⟨x.1.τ, off⟩ : LeanVM.Protocol.Verifier.Placement), pt.take x.1.τ))
      | _ => pure none) (sideColsG x.1 s) >>= fun l ↦ pure (l.filterMap id)) tabs.zipIdx >>= fun L ↦
    pure L.flatten

theorem hs_partsC {z : C2} (hz : z.val M = 0) (tabs : List Tab) (forms : List (List FormC)) (pt : List C2)
    (tot : List E2) (s : ℕ) :
    Hs c M (partsC z tabs forms pt s) fun ps ↦
      ps.map (evP M) = mbPartsG tabs ⟨pt.map (ev2 M), forms.map (·.map (evF M)), tot⟩ s := by
  refine hs_bind (hs_mapB2 _ (fun x : Tab × ℕ ↦ (sideColsG x.1 s).filterMap fun cc ↦ match x.1.cols[cc]? with
      | some (ColSrc.com _ off) => some (Mb.coefG (evF M (formAt forms x.2 s)) cc, (⟨x.1.τ, off⟩ : LeanVM.Protocol.Verifier.Placement),
          (pt.map (ev2 M)).take x.1.τ)
      | _ => none) (·.map (evP M)) (fun x ↦ hs_bind (hs_mapB2 _ (fun cc ↦ match x.1.cols[cc]? with
      | some (ColSrc.com _ off) => some (Mb.coefG (evF M (formAt forms x.2 s)) cc, (⟨x.1.τ, off⟩ : LeanVM.Protocol.Verifier.Placement),
          (pt.map (ev2 M)).take x.1.τ)
      | _ => none) (Option.map (evP M)) (fun cc ↦ ?_) _) fun l hl ↦ hs_pure ?_) _) fun L hL ↦ hs_pure ?_
  · rcases hcol : x.1.cols[cc]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩)
    · exact hs_pure rfl
    · exact hs_bind (hs_coefC hz _ cc) fun k hk ↦ hs_pure (by simp [evP, hk, List.map_take])
    · exact hs_pure rfl
  · rw [map_filterMap_id, hl, filterMap_id_map]
  · rw [List.map_flatten, hL, mbPartsG, List.flatMap]
    congr 1
    refine List.map_congr_left fun x _ ↦ ?_
    simp only [formG_evR]
    rfl

theorem sum_range_list (n : ℕ) (g : ℕ → E2) : ∑ x ∈ Finset.range n, g x = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- `hs_mapB2` with membership. -/
theorem hs_mapB2m {α β γ : Type} (f : α → BM β) (F : α → γ) (g : β → γ) :
    ∀ l : List α, (∀ a ∈ l, Hs c M (f a) fun r ↦ g r = F a) → Hs c M (mapB f l) fun rs ↦ rs.map g = l.map F
  | [], _ => hs_pure rfl
  | a :: l, h => hs_bind (h a List.mem_cons_self) fun r hr ↦
      hs_bind (hs_mapB2m f F g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) fun rs hrs ↦
        hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

/-- `acc + Σ_{x ∈ xs} f(x)·eqT[x]`, one row pair per `x` (`g2Lin`). -/
def mleFrom (z : C2) (eqT : List C2) (f : ℕ → FK) : C2 → List ℕ → BM C2
  | acc, [] => pure acc
  | acc, x :: xs => g2Lin (f x) 0 acc (eqT.getD x z) >>= fun a ↦ mleFrom z eqT f a xs

theorem hs_mleFrom {z : C2} (hz : z.val M = 0) {eqT : List C2} {τ : ℕ} {p : List E2}
    (hT : eqT.map (ev2 M) = (List.range (2 ^ τ)).map (eqAtF p)) (f : ℕ → FK) :
    ∀ (xs : List ℕ) (acc : C2), (∀ x ∈ xs, x < 2 ^ τ) →
      Hs c M (mleFrom z eqT f acc xs) fun r ↦ ev2 M r = ev2 M acc + (xs.map fun x ↦ eqAtF p x * kG (f x)).sum
  | [], acc, _ => hs_pure (by simp)
  | x :: xs, acc, hx => hs_bind (hs_g2Lin _ _ _ _) fun a ha ↦
      hs_mono (hs_mleFrom hz hT f xs a fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)) fun r hr ↦ by
        have hxl : x < 2 ^ τ := hx x List.mem_cons_self
        rw [hr, ev2_lin0 ha, getD_ev2 hT (ev2_of_zero hz), List.getD_eq_getElem _ _ (by simpa using hxl),
          List.getElem_map, List.getElem_range, List.map_cons, List.sum_cons]
        ring

/-- `Σ_{x < 2^τ} eq(pt, x)·f(x)` from the `eq` table `eqT` of `pt` (`mleFixG`): one row pair per `x`. -/
def mleC (z : C2) (eqT : List C2) (τ : ℕ) (f : ℕ → FK) : BM C2 := mleFrom z eqT f z (List.range (2 ^ τ))

theorem hs_mleC {z : C2} (hz : z.val M = 0) {eqT : List C2} {τ : ℕ} {p : List E2}
    (hT : eqT.map (ev2 M) = (List.range (2 ^ τ)).map (eqAtF p)) (f : ℕ → FK) :
    Hs c M (mleC z eqT τ f) fun r ↦ ev2 M r = mleFixG τ f p :=
  hs_mono (hs_mleFrom hz hT f _ z fun x hx ↦ List.mem_range.mp hx) fun r hr ↦ by
    rw [hr, ev2_of_zero hz, zero_add, mleFixG, sum_range_list]

/-! ## The `eq` tables of `ζ_{<τ}` and the fixed columns' extensions -/

/-- A column is fixed. -/
def isFixB : ColSrc → Bool
  | .fix _ _ => true
  | _ => false

/-- The log-heights of the tables with a fixed column. -/
def fixTaus (tabs : List Tab) : List ℕ := ((tabs.filter fun t ↦ t.cols.any isFixB).map (·.τ)).eraseDups

/-- An `eq` table entry: `(τ, eq(ζ_{<τ}, ·))`. -/
def TabOk (M : Mem) (P : List E2) (e : ℕ × List C2) : Prop :=
  e.2.map (ev2 M) = (List.range (2 ^ e.1)).map (eqAtF (P.take e.1))

/-- The `eq` tables of `ζ_{<τ}` for `τ ∈ τs`, `τ ≤ |ζ|`, by the trie (`os` the cells `1 + ζ`). -/
def eqTabsC (z one : C2) (pt os : List C2) (τs : List ℕ) : BM (List (ℕ × List C2)) :=
  mapB (fun τ ↦ eqTabG z one (pt.take τ) (os.take τ) >>= fun T ↦ pure (τ, T))
    (τs.filter fun τ ↦ decide (τ ≤ pt.length))

theorem hs_eqTabsC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {pt os : List C2}
    (hos : OnesOk M z pt os) (τs : List ℕ) :
    Hs c M (eqTabsC z one pt os τs) fun L ↦ ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e := by
  refine hs_mono (hs_mapB2m _ (fun τ ↦ (τ, (List.range (2 ^ τ)).map (eqAtF ((pt.map (ev2 M)).take τ))))
    (fun e : ℕ × List C2 ↦ (e.1, e.2.map (ev2 M))) _ fun τ hτ ↦ ?_) fun L hL e he ↦ ?_
  · have hτ' : τ ≤ pt.length := by simpa using (List.mem_filter.mp hτ).2
    refine hs_bind (hs_eqTabG hz hone (hos.take τ)) fun T hT ↦ hs_pure ?_
    show (τ, T.map (ev2 M)) = (τ, (List.range (2 ^ τ)).map (eqAtF ((pt.map (ev2 M)).take τ)))
    rw [hT, List.length_take, min_eq_left hτ', List.map_take]
  · have hm : (e.1, e.2.map (ev2 M)) ∈ L.map fun e : ℕ × List C2 ↦ (e.1, e.2.map (ev2 M)) :=
      List.mem_map_of_mem he
    rw [hL] at hm
    obtain ⟨τ, -, hτe⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at hτe
    rw [TabOk, ← hτe.2, ← hτe.1]

/-- The `eq` table of `ζ_{<τ}`: `L`'s, or `eqAtG` per index when `L` lacks it. -/
def eqTabAt (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (τ : ℕ) : BM (List C2) :=
  match L.find? (fun e ↦ e.1 == τ) with
  | some e => pure e.2
  | none => mapB (eqAtG z one (pt.take τ)) (List.range (2 ^ τ))

theorem hs_eqTabAt {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (τ : ℕ) :
    Hs c M (eqTabAt z one pt L τ) fun T ↦
      T.map (ev2 M) = (List.range (2 ^ τ)).map (eqAtF ((pt.map (ev2 M)).take τ)) := by
  unfold eqTabAt
  split
  · rename_i e he
    have hk : e.1 = τ := by simpa using List.find?_some he
    have h := hL e (List.mem_of_find?_eq_some he)
    unfold TabOk at h
    exact hs_pure (by rw [h, hk])
  · exact hs_mapB_eq _ fun i _ ↦ hs_mono (hs_eqAtG hz hone _ i) fun r hr ↦ by rw [hr, List.map_take]

/-- A fixed column's extension at `ζ_{<τ}` (`0` for the other columns). -/
noncomputable def mleV (P : List E2) (t : Tab) (cc : ℕ) : E2 :=
  match t.cols[cc]? with
  | some (ColSrc.fix fc _) => mleFixG t.τ fc (P.take t.τ)
  | _ => 0

/-- Table `t`'s fixed columns' extensions, once per table (`z` for the other columns). -/
def mlesC (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (t : Tab) : BM (List C2) :=
  mapB (fun cc ↦ match t.cols[cc]? with
    | some (ColSrc.fix fc _) => eqTabAt z one pt L t.τ >>= fun T ↦ mleC z T t.τ fc
    | _ => pure z) (List.range t.w)

theorem hs_mlesC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (t : Tab) :
    Hs c M (mlesC z one pt L t) fun ms ↦ ms.map (ev2 M) = (List.range t.w).map (mleV (pt.map (ev2 M)) t) := by
  refine hs_mapB_eq _ fun cc _ ↦ ?_
  unfold mleV
  rcases hcol : t.cols[cc]? with _ | (⟨rec, off⟩ | ⟨fc, ev⟩)
  · exact hs_pure (ev2_of_zero hz)
  · exact hs_pure (ev2_of_zero hz)
  · exact hs_bind (hs_eqTabAt hz hone pt hL t.τ) fun T hT ↦ hs_mleC hz hT fc

/-- `constG t f pt` with cell coefficients (`ms` the fixed columns' extensions, `mlesC`). -/
def constC (z : C2) (t : Tab) (ms : List C2) (f : FormC) : BM C2 :=
  mapB (fun m : List ℕ × C2 ↦ match m.1 with
    | [] => pure m.2
    | [cc] => match t.cols[cc]? with
      | some (ColSrc.fix _ _) => g2Mul m.2 (ms.getD cc z) z
      | _ => pure z
    | _ => pure z) f >>= sumNZ z

theorem hs_constC {z : C2} (hz : z.val M = 0) (t : Tab) {ms : List C2} {P : List E2}
    (hms : ms.map (ev2 M) = (List.range t.w).map (mleV P t)) (f : FormC) :
    Hs c M (constC z t ms f) fun r ↦ ev2 M r = constG t (evF M f) (P.take t.τ) := by
  refine hs_bind (hs_mapB2 _ (fun m : List ℕ × C2 ↦ match m.1 with
      | [] => ev2 M m.2
      | [cc] => match t.cols[cc]? with
        | some (ColSrc.fix fc _) => ev2 M m.2 * mleFixG t.τ fc (P.take t.τ)
        | _ => 0
      | _ => 0) (ev2 M) (fun m ↦ ?_) f) fun l hl ↦ hs_mono (hs_sumNZ hz l) fun r hr ↦ ?_
  · rcases m with ⟨_ | ⟨cc, _ | ⟨d, ds⟩⟩, w⟩
    · exact hs_pure rfl
    · simp only
      rcases hcol : t.cols[cc]? with _ | (⟨rec, off⟩ | ⟨fc, ev⟩)
      · exact hs_pure (ev2_of_zero hz)
      · exact hs_pure (ev2_of_zero hz)
      · refine hs_mono (hs_g2Mul w _ z) fun r hr ↦ ?_
        have hcc : cc < t.w := by
          rcases Nat.lt_or_ge cc t.cols.length with h | h
          · exact h
          · simp [List.getElem?_eq_none h] at hcol
        rw [ev2_mul hr, ev2_of_zero hz, add_zero, getD_ev2 hms (ev2_of_zero hz),
          List.getD_eq_getElem _ _ (by simpa using hcc), List.getElem_map, List.getElem_range, mleV, hcol]
    · exact hs_pure (ev2_of_zero hz)
  · rw [hr, hl, constG, evF, List.map_map]
    rfl

/-- Table `x`'s three constants (`constC` per side), its fixed columns' extensions computed once. -/
def tabConstC (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (forms : List (List FormC)) (x : Tab × ℕ) :
    BM (List C2) :=
  mlesC z one pt L x.1 >>= fun ms ↦ mapB (fun s ↦ constC z x.1 ms (formAt forms x.2 s)) (List.range 3)

theorem hs_tabConstC {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (forms : List (List FormC))
    (x : Tab × ℕ) :
    Hs c M (tabConstC z one pt L forms x) fun cs ↦ cs.map (ev2 M) =
      (List.range 3).map fun s ↦ constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ) :=
  hs_bind (hs_mlesC hz hone pt hL x.1) fun _ hms ↦ hs_mapB_eq _ fun _ _ ↦ hs_constC hz x.1 hms _

/-- `mbValueG tabs r s`: the side's total plus every table's constant (`consts`, `tabConstC`). -/
def valC (z : C2) (consts : List (List C2)) (tot : List C2) (s : ℕ) : BM C2 :=
  sumNZ z (consts.map (·.getD s z)) >>= fun S ↦ g2Add (tot.getD s z) S

theorem hs_valC {z : C2} (hz : z.val M = 0) (tabs : List Tab) {consts : List (List C2)} {pt : List C2}
    (forms : List (List FormC))
    (hcs : consts.map (·.map (ev2 M)) = tabs.zipIdx.map fun x ↦ (List.range 3).map fun s ↦
      constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ))
    (tot : List C2) {s : ℕ} (hs : s < 3) :
    Hs c M (valC z consts tot s) fun r ↦
      ev2 M r = mbValueG tabs ⟨pt.map (ev2 M), forms.map (·.map (evF M)), tot.map (ev2 M)⟩ s := by
  refine hs_bind (hs_sumNZ hz _) fun S hS ↦ hs_mono (hs_g2Add _ S) fun r hr ↦ ?_
  have hm : (consts.map (·.getD s z)).map (ev2 M) =
      tabs.zipIdx.map fun x ↦ constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ) := by
    have h1 : (consts.map (·.getD s z)).map (ev2 M) = (consts.map (·.map (ev2 M))).map (·.getD s 0) := by
      simp only [List.map_map]
      refine List.map_congr_left fun l _ ↦ ?_
      show ev2 M (l.getD s z) = (l.map (ev2 M)).getD s 0
      exact getD_ev2 rfl (ev2_of_zero hz) s
    rw [h1, hcs, List.map_map]
    refine List.map_congr_left fun x _ ↦ ?_
    show ((List.range 3).map _).getD s 0 = _
    rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map, List.getElem_range]
  rw [ev2_add hr, getD_ev2 rfl (ev2_of_zero hz), hS, hm, mbValueG]
  congr 2
  refine List.map_congr_left fun x _ ↦ ?_
  simp only [formG_evR]

/-! ## Memos (WP MBS, second cut): one computation per equal key -/

/-- `f` on every element, threading a state. -/
def mapS {σ α β : Type} (f : σ → α → BM (σ × β)) : σ → List α → BM (σ × List β)
  | st, [] => pure (st, [])
  | st, a :: as => f st a >>= fun r ↦ mapS f r.1 as >>= fun rs ↦ pure (rs.1, r.2 :: rs.2)

theorem hs_mapS {σ α β γ : Type} (Inv : σ → Prop) (f : σ → α → BM (σ × β)) (F : α → γ) (g : β → γ)
    (hf : ∀ st a, Inv st → Hs c M (f st a) fun r ↦ Inv r.1 ∧ g r.2 = F a) :
    ∀ (st : σ) (l : List α), Inv st → Hs c M (mapS f st l) fun r ↦ Inv r.1 ∧ r.2.map g = l.map F
  | st, [], h => hs_pure ⟨h, rfl⟩
  | st, a :: as, h => hs_bind (hf st a h) fun r hr ↦ hs_bind (hs_mapS Inv f F g hf r.1 as hr.1) fun rs hrs ↦
      hs_pure ⟨hrs.1, by rw [List.map_cons, List.map_cons, hr.2, hrs.2]⟩

/-- `comp` once per `key`: the memo's result for an equal key, else `comp` (recorded). -/
def memoB {κ β : Type} [DecidableEq κ] (key : κ) (comp : BM β) (memo : List (κ × β)) :
    BM (List (κ × β) × β) :=
  match memo.find? (fun e ↦ decide (e.1 = key)) with
  | some e => pure (memo, e.2)
  | none => comp >>= fun b ↦ pure ((key, b) :: memo, b)

theorem hs_memoB {κ β : Type} [DecidableEq κ] (P : κ → β → Prop) (key : κ) {comp : BM β}
    (hc : Hs c M comp (P key)) (memo : List (κ × β)) (hm : ∀ e ∈ memo, P e.1 e.2) :
    Hs c M (memoB key comp memo) fun r ↦ (∀ e ∈ r.1, P e.1 e.2) ∧ P key r.2 := by
  unfold memoB
  split
  · rename_i e he
    have hk : e.1 = key := by simpa using List.find?_some he
    have h := hm e (List.mem_of_find?_eq_some he)
    rw [hk] at h
    exact hs_pure ⟨hm, h⟩
  · refine hs_bind hc fun b hb ↦ hs_pure ⟨fun e he ↦ ?_, hb⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact hb
    · exact hm e he

theorem map_of_map {X Y Z U : Type} (f : X → Z) (g : Y → Z) (u : X → U) (v : Y → U)
    (huv : ∀ a b, f a = g b → u a = v b) : ∀ (A : List X) (B : List Y), A.map f = B.map g → A.map u = B.map v
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: A, b :: B, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨huv a b h.1, map_of_map f g u v huv A B h.2⟩

/-! ### Block weights: one trie per distinct request list (push and pull stack the same blocks) -/

/-- The trie requests of a side's stacked blocks. -/
def wReq (bs : List VBlockC) : List (ℕ × ℕ) := (stk VBlockC.κ (sortC bs) 0).map fun bo ↦ (bo.1.κ, bo.2 / 2 ^ bo.1.κ)

/-- A trie's cells are its requests' weights. -/
def WOk (M : Mem) (P : List E2) (Q : List (ℕ × ℕ)) (W : List C2) : Prop :=
  W.map (ev2 M) = Q.map fun q ↦ eqAtF (P.drop q.1) q.2

/-- `sideWG` with a memo of tries by their requests. -/
def sideWGm (z one : C2) (pt os : List C2) (memo : List (List (ℕ × ℕ) × List C2)) (bs : List VBlockC) :
    BM (List (List (ℕ × ℕ) × List C2) × List (VBlockC × C2)) :=
  memoB (wReq bs) (eqHiG z one pt os (wReq bs)) memo >>= fun r ↦
    pure (r.1, ((stk VBlockC.κ (sortC bs) 0).map (·.1)).zip r.2)

theorem hs_sideWGm {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2) {os : List C2}
    (hos : OnesOk M z pt os) (memo : List (List (ℕ × ℕ) × List C2))
    (hm : ∀ e ∈ memo, WOk M (pt.map (ev2 M)) e.1 e.2) (bs : List VBlockC) :
    Hs c M (sideWGm z one pt os memo bs) fun r ↦ (∀ e ∈ r.1, WOk M (pt.map (ev2 M)) e.1 e.2) ∧
      r.2.map (evBW M) = (stackBlocksG (bs.map (evB M))).map fun bo ↦
        (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ (pt.map (ev2 M))) := by
  refine hs_bind (hs_memoB (WOk M (pt.map (ev2 M))) _ (hs_eqHiG hz hone hos _) memo hm) fun r hr ↦
    hs_pure ⟨hr.1, ?_⟩
  have hW : r.2.map (ev2 M) = (stk VBlockC.κ (sortC bs) 0).map fun bo ↦
      eqAtF ((pt.map (ev2 M)).drop bo.1.κ) (bo.2 / 2 ^ bo.1.κ) := by
    have h := hr.2
    unfold WOk wReq at h
    rw [h, List.map_map]
    rfl
  show (((stk VBlockC.κ (sortC bs) 0).map (·.1)).zip r.2).map (evBW M) = _
  rw [zip_map_ev _ _ _ _ hW, stackBlocksG_map, List.map_map]
  refine List.map_congr_left fun bo _ ↦ ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, eqAboveG_eq]
  rfl

/-! ### Weighted forms: one product per distinct (weight, coefficient) pair -/

/-- A memo of products `w·a`. -/
abbrev PMemo : Type := List ((C2 × C2) × C2)

/-- A product entry. -/
def PrOk (M : Mem) (k : C2 × C2) (r : C2) : Prop := ev2 M r = ev2 M k.1 * ev2 M k.2

/-- A weighted block's table and form `w·form` (`bucketG`'s terms). -/
def wFormV (bw : VBlockG × E2) : ℕ × FormG := (bw.1.tab, ⟨bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)⟩)

/-- A block's table and weighted form, the products memoized. -/
def wFormS (z one : C2) (memo : PMemo) (bw : VBlockC × C2) : BM (PMemo × (ℕ × FormC)) :=
  mapS (fun m (t : List ℕ × C2) ↦ memoB (bw.2, t.2) (mulC z one bw.2 t.2) m >>= fun r ↦ pure (r.1, (t.1, r.2)))
    memo bw.1.form >>= fun r ↦ pure (r.1, (bw.1.tab, r.2))

theorem hs_wFormS {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (memo : PMemo)
    (hm : ∀ e ∈ memo, PrOk M e.1 e.2) (bw : VBlockC × C2) :
    Hs c M (wFormS z one memo bw) fun r ↦ (∀ e ∈ r.1, PrOk M e.1 e.2) ∧
      (r.2.1, evF M r.2.2) = wFormV (evBW M bw) := by
  refine hs_bind (hs_mapS (fun m : PMemo ↦ ∀ e ∈ m, PrOk M e.1 e.2) _
    (fun t : List ℕ × C2 ↦ (t.1, ev2 M bw.2 * ev2 M t.2)) (fun t : List ℕ × C2 ↦ (t.1, ev2 M t.2))
    (fun m t hm' ↦ hs_bind (hs_memoB (PrOk M) _ (hs_mulC hz hone _ _) m hm') fun r hr ↦
      hs_pure ⟨hr.1, ?_⟩) memo _ hm) fun r hr ↦ hs_pure ⟨hr.1, ?_⟩
  · have h : ev2 M r.2 = ev2 M bw.2 * ev2 M t.2 := hr.2
    show (t.1, ev2 M r.2) = _
    rw [h]
  · show (bw.1.tab, evF M r.2) = wFormV (evBW M bw)
    simp only [wFormV, evBW, evB, evF, hr.2, List.map_map]
    rfl

/-- Table `j`'s bucket of a weighted side (no rows). -/
def bucketF (ws : List (ℕ × FormC)) (j : ℕ) : FormC := ((ws.filter fun p ↦ p.1 == j).reverse).flatMap (·.2)

theorem bucketF_ev (j : ℕ) (ws : List (ℕ × FormC)) (s : List (VBlockG × E2))
    (h : ws.map (fun p ↦ (p.1, evF M p.2)) = s.map wFormV) : evF M (bucketF ws j) = ⟨bucketG s j⟩ := by
  have e1 : evF M (bucketF ws j) =
      ⟨(((ws.map fun p ↦ (p.1, evF M p.2)).filter fun p ↦ p.1 == j).reverse).flatMap (·.2.terms)⟩ := by
    simp only [bucketF, evF, List.map_flatMap, List.filter_map, Function.comp_def]
    rw [← List.map_reverse, List.flatMap_map]
  rw [e1, h]
  simp only [bucketG, List.filter_map, Function.comp_def, wFormV]
  rw [← List.map_reverse, List.flatMap_map]
  try rfl

/-! ### Totals: one weight sum per distinct weight list -/

/-- A sum entry. -/
def SumOk (M : Mem) (l : List C2) (r : C2) : Prop := ev2 M r = sumF (l.map (ev2 M))

/-- Side `k`'s total `v_k + 1 + Σ_b w_b`, the weight sum memoized by its cells. -/
def totCS (z one : C2) (sd : List (List (VBlockC × C2))) (vs : List C2) (memo : List (List C2 × C2)) (k : ℕ) :
    BM (List (List C2 × C2) × C2) :=
  memoB ((sd.getD k []).map (·.2)) (sumG z ((sd.getD k []).map (·.2))) memo >>= fun r ↦
    g2Add (vs.getD k z) one >>= fun a ↦ g2Add a r.2 >>= fun t ↦ pure (r.1, t)

theorem hs_totCS {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {sd : List (List (VBlockC × C2))}
    {sides : List (List (VBlockG × E2))} (hsd : sd.map (·.map (evBW M)) = sides) (vs : List C2)
    (memo : List (List C2 × C2)) (hm : ∀ e ∈ memo, SumOk M e.1 e.2) (k : ℕ) :
    Hs c M (totCS z one sd vs memo k) fun r ↦ (∀ e ∈ r.1, SumOk M e.1 e.2) ∧
      ev2 M r.2 = (vs.map (ev2 M)).getD k 0 + 1 + sumF ((sides.getD k []).map (·.2)) := by
  refine hs_bind (hs_memoB (SumOk M) _ (hs_sumG hz _) memo hm) fun r hr ↦ hs_bind (hs_g2Add _ one) fun a ha ↦
    hs_bind (hs_g2Add a r.2) fun t ht ↦ hs_pure ⟨hr.1, ?_⟩
  have hsw : ev2 M r.2 = sumF (((sd.getD k []).map (·.2)).map (ev2 M)) := hr.2
  show ev2 M t = _
  rw [ev2_add ht, ev2_add ha, getD_ev2 rfl (ev2_of_zero hz), hone, hsw, ← hsd]
  congr 2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases sd[k]? <;> simp [evBW]

/-! ### Fixed columns' extensions: one table per `τ`, the others by their ratio -/

/-- A memo of extensions `(τ, f, cell)`. -/
abbrev MMemo : Type := List (ℕ × (ℕ → FK) × C2)

/-- An extension entry. -/
def MOk (M : Mem) (P : List E2) (e : ℕ × (ℕ → FK) × C2) : Prop :=
  ev2 M e.2.2 = mleFixG e.1 e.2.1 (P.take e.1)

/-- The ratio `f(0)/g(0)`. -/
def ratioK (f g : ℕ → FK) : FK := f 0 * (g 0)⁻¹

/-- `f = k·g` on the cube of `τ` (`k = ratioK f g`), checked. -/
def ratioB (τ : ℕ) (f g : ℕ → FK) : Bool := (List.range (2 ^ τ)).all fun x ↦ f x == ratioK f g * g x

theorem kG_mul (a b : FK) : kG (a * b) = kG a * kG b := by
  have h : FE2.ofK (a * b) = FE2.ofK a * FE2.ofK b := map_mul FE2.ofKRingHom a b
  simp only [kG, h, FE2.fe2_mul_eq]

theorem mleFixG_ratio {τ : ℕ} {f g : ℕ → FK} (h : ratioB τ f g = true) (p : List E2) :
    mleFixG τ f p = kG (ratioK f g) * mleFixG τ g p := by
  unfold mleFixG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := List.all_eq_true.mp h x (List.mem_range.mpr (Finset.mem_range.mp hx))
  rw [beq_iff_eq.mp hx', kG_mul]
  ring

/-- A fixed column's extension: `k·` an earlier one of the same `τ` when `f = k·f₀` (one row pair), else from the
`eq` table (recorded). -/
def mleShared (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (memo : MMemo) (τ : ℕ) (f : ℕ → FK) :
    BM (MMemo × C2) :=
  match memo.find? (fun e ↦ e.1 == τ && ratioB τ f e.2.1) with
  | some e => g2Lin (ratioK f e.2.1) 0 z e.2.2 >>= fun r ↦ pure (memo, r)
  | none => eqTabAt z one pt L τ >>= fun T ↦ mleC z T τ f >>= fun r ↦ pure ((τ, f, r) :: memo, r)

theorem hs_mleShared {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (memo : MMemo)
    (hm : ∀ e ∈ memo, MOk M (pt.map (ev2 M)) e) (τ : ℕ) (f : ℕ → FK) :
    Hs c M (mleShared z one pt L memo τ f) fun r ↦ (∀ e ∈ r.1, MOk M (pt.map (ev2 M)) e) ∧
      ev2 M r.2 = mleFixG τ f ((pt.map (ev2 M)).take τ) := by
  unfold mleShared
  split
  · rename_i e he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have he' : ev2 M e.2.2 = mleFixG e.1 e.2.1 ((pt.map (ev2 M)).take e.1) := hm e (List.mem_of_find?_eq_some he)
    refine hs_bind (hs_g2Lin _ _ _ _) fun r hr ↦ hs_pure ⟨hm, ?_⟩
    show ev2 M r = _
    rw [ev2_lin0 hr, ev2_of_zero hz, zero_add, he', hp.1, mleFixG_ratio hp.2]
  · refine hs_bind (hs_eqTabAt hz hone pt hL τ) fun T hT ↦ hs_bind (hs_mleC hz hT f) fun r hr ↦
      hs_pure ⟨fun e he ↦ ?_, hr⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact hr
    · exact hm e he

/-- Table `t`'s fixed columns' extensions with the memo (`z` for the other columns). -/
def mlesS (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (memo : MMemo) (t : Tab) : BM (MMemo × List C2) :=
  mapS (fun m cc ↦ match t.cols[cc]? with
    | some (ColSrc.fix fc _) => mleShared z one pt L m t.τ fc
    | _ => pure (m, z)) memo (List.range t.w)

theorem hs_mlesS {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (memo : MMemo)
    (hm : ∀ e ∈ memo, MOk M (pt.map (ev2 M)) e) (t : Tab) :
    Hs c M (mlesS z one pt L memo t) fun r ↦ (∀ e ∈ r.1, MOk M (pt.map (ev2 M)) e) ∧
      r.2.map (ev2 M) = (List.range t.w).map (mleV (pt.map (ev2 M)) t) := by
  unfold mlesS
  refine hs_mapS (fun m : MMemo ↦ ∀ e ∈ m, MOk M (pt.map (ev2 M)) e) _ (mleV (pt.map (ev2 M)) t) (ev2 M)
    (fun m cc hm' ↦ ?_) memo _ hm
  unfold mleV
  rcases hcol : t.cols[cc]? with _ | (⟨rec, off⟩ | ⟨fc, ev⟩)
  · exact hs_pure ⟨hm', ev2_of_zero hz⟩
  · exact hs_pure ⟨hm', ev2_of_zero hz⟩
  · exact hs_mleShared hz hone pt hL m hm' t.τ fc

/-- Table `x`'s three constants, its fixed columns' extensions from the memo. -/
def tabConstS (z one : C2) (pt : List C2) (L : List (ℕ × List C2)) (forms : List (List FormC)) (memo : MMemo)
    (x : Tab × ℕ) : BM (MMemo × List C2) :=
  mlesS z one pt L memo x.1 >>= fun r ↦
    mapB (fun s ↦ constC z x.1 r.2 (formAt forms x.2 s)) (List.range 3) >>= fun cs ↦ pure (r.1, cs)

theorem hs_tabConstS {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) (pt : List C2)
    {L : List (ℕ × List C2)} (hL : ∀ e ∈ L, TabOk M (pt.map (ev2 M)) e) (forms : List (List FormC))
    (memo : MMemo) (hm : ∀ e ∈ memo, MOk M (pt.map (ev2 M)) e) (x : Tab × ℕ) :
    Hs c M (tabConstS z one pt L forms memo x) fun r ↦ (∀ e ∈ r.1, MOk M (pt.map (ev2 M)) e) ∧
      r.2.map (ev2 M) =
        (List.range 3).map fun s ↦ constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ) :=
  hs_bind (hs_mlesS hz hone pt hL memo hm x.1) fun _ hr ↦
    hs_bind (hs_mapB_eq _ fun _ _ ↦ hs_constC hz x.1 hr.2 _) fun _ hcs ↦ hs_pure ⟨hr.1, hcs⟩

/-- The largest log-height. -/
def maxτ (tabs : List Tab) : ℕ := (tabs.map (·.τ)).foldl max 0

theorem le_foldl_max : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a y)
    refine ⟨(le_max_left a y).trans h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a x).trans h1
    · exact h2 x hx

theorem τ_le_maxτ {tabs : List Tab} {t : Tab} (ht : t ∈ tabs) : t.τ ≤ maxτ tabs :=
  (le_foldl_max _ 0).2 _ (List.mem_map_of_mem ht)

/-! ## The gadget and its HAR -/

/-- **The mini-bus claims' parts and values** (claims 50–52) from the walk's output cells `α`, `β`, `ζ` and the
three values `v`, for the tables `tabs`: per side `s < 3`, the parts of `mbPartsG` and the value of `mbValueG`.
WP MBS: block weights and `eq` tables by the trie (`eqHiG`), constant coefficients without products; memos (`memoB`)
share the tries, products and weight sums of push and pull, and the fixed columns' extensions by their ratio. -/
def mbPreG (tabs : List Tab) (al : List C2) (be : C2) (pt vs : List C2) (gate : Cell) :
    BM (List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2) :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦
  eqsG z one al >>= fun e ↦
  sideBlocksC z one e be tabs >>= fun bl ↦
  onesG pt >>= fun os ↦
  mapS (sideWGm z one pt os) [] bl >>= fun rw ↦ pure rw.2 >>= fun sd ↦
  mapS (fun m s ↦ mapS (wFormS z one) m s) [] sd >>= fun rf ↦
  pure ((List.range tabs.length).map fun j ↦ rf.2.map fun ws ↦ bucketF ws j) >>= fun forms ↦
  mapS (totCS z one sd vs) [] (List.range 3) >>= fun rt ↦ pure rt.2 >>= fun tot ↦
  eqTabsC z one pt os (fixTaus tabs) >>= fun L ↦
  mapS (tabConstS z one pt L forms) [] tabs.zipIdx >>= fun rc ↦ pure rc.2 >>= fun consts ↦
  mapB (partsC z tabs forms pt) (List.range 3) >>= fun ps ↦
  mapB (valC z consts tot) (List.range 3) >>= fun vals ↦
  pure (ps, vals)

theorem getD_map_nil {α β : Type} (f : α → β) (l : List (List α)) (i : ℕ) :
    (l.getD i []).map f = (l.map (·.map f)).getD i [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- **The HAR of `mbPreG`**: where its rows hold, side `s`'s parts are `mbPartsG tabs r s` (as `partsV`) and its
value is `mbValueG tabs r s`, `r` the bus result `busFinalG` of the cells' values. -/
theorem hs_mbPreG (tabs : List Tab) (al : List C2) (be : C2) (pt vs : List C2) (gate : Cell) :
    Hs c M (mbPreG tabs al be pt vs gate) fun out ↦
      out.1.map (partsV M) = (List.range 3).map (mbPartsG tabs
        (busFinalG tabs (al.map (ev2 M)) (ev2 M be) (pt.map (ev2 M)) (vs.map (ev2 M)))) ∧
      out.2.map (ev2 M) = (List.range 3).map (mbValueG tabs
        (busFinalG tabs (al.map (ev2 M)) (ev2 M be) (pt.map (ev2 M)) (vs.map (ev2 M)))) := by
  refine hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone' ↦ ?_
  have hone : ev2 M one = 1 := ev2_one' hone'
  refine hs_bind (hs_eqsG hz hone al) fun e he ↦ ?_
  have he' : ∀ i, ev2 M (e.getD i z) = (eqKernelF (al.map (ev2 M))).getD i 0 :=
    getD_ev2 he (ev2_of_zero hz)
  refine hs_bind (hs_sideBlocksC hz hone he' be tabs) fun bl hbl ↦ ?_
  set sidesV := sidesG tabs (al.map (ev2 M)) (ev2 M be) (pt.map (ev2 M)) with hsV
  refine hs_bind (hs_onesG pt z) fun os hos ↦ ?_
  refine hs_bind (hs_mapS (fun m : List (List (ℕ × ℕ) × List C2) ↦ ∀ e ∈ m, WOk M (pt.map (ev2 M)) e.1 e.2)
      (sideWGm z one pt os) (fun bs ↦ (stackBlocksG (bs.map (evB M))).map fun bo ↦
        (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ (pt.map (ev2 M)))) (·.map (evBW M))
      (fun m bs hm ↦ hs_sideWGm hz hone pt hos m hm bs) [] bl (by simp)) fun rw hrw ↦
    hs_bind (hs_pure (P := fun sd ↦ sd = rw.2) rfl) fun sd hsdw ↦ ?_
  have hsd : sd.map (·.map (evBW M)) = sidesV := by
    rw [hsdw, hrw.2, hsV, sidesG, ← hbl, List.map_map]
    rfl
  refine hs_bind (hs_mapS (fun m : PMemo ↦ ∀ e ∈ m, PrOk M e.1 e.2) (fun m s ↦ mapS (wFormS z one) m s)
      (fun s : List (VBlockC × C2) ↦ s.map fun bw ↦ wFormV (evBW M bw)) (·.map fun p ↦ (p.1, evF M p.2))
      (fun m s hm ↦ hs_mapS _ (wFormS z one) (fun bw ↦ wFormV (evBW M bw)) (fun p ↦ (p.1, evF M p.2))
        (fun m' bw hm' ↦ hs_wFormS hz hone m' hm' bw) m s hm) [] sd (by simp)) fun rf hrf ↦
    hs_bind (hs_pure (P := fun forms ↦ forms = (List.range tabs.length).map fun j ↦ rf.2.map fun ws ↦ bucketF ws j)
      rfl) fun forms hfe ↦ ?_
  have hforms : forms.map (·.map (evF M)) =
      (List.range tabs.length).map fun j ↦ sidesV.map fun s ↦ (⟨bucketG s j⟩ : FormG) := by
    rw [hfe, List.map_map]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [List.map_map, Function.comp_def]
    refine map_of_map (fun ws ↦ ws.map fun p ↦ (p.1, evF M p.2)) (fun s ↦ s.map wFormV) _ _
      (fun ws s h ↦ bucketF_ev j ws s h) rf.2 sidesV ?_
    rw [hrf.2, ← hsd]
    simp only [List.map_map, Function.comp_def]
  refine hs_bind (hs_mapS (fun m : List (List C2 × C2) ↦ ∀ e ∈ m, SumOk M e.1 e.2) (totCS z one sd vs)
      (fun k ↦ (vs.map (ev2 M)).getD k 0 + 1 + sumF ((sidesV.getD k []).map (·.2))) (ev2 M)
      (fun m k hm ↦ hs_totCS hz hone hsd vs m hm k) [] _ (by simp)) fun rt hrt ↦
    hs_bind (hs_pure (P := fun tot ↦ tot = rt.2) rfl) fun tot hte ↦ ?_
  have htot : tot.map (ev2 M) = (List.range 3).map fun k ↦
      (vs.map (ev2 M)).getD k 0 + 1 + sumF ((sidesV.getD k []).map (·.2)) := by
    rw [hte]
    exact hrt.2
  have hr : busFinalG tabs (al.map (ev2 M)) (ev2 M be) (pt.map (ev2 M)) (vs.map (ev2 M)) =
      ⟨pt.map (ev2 M), forms.map (·.map (evF M)), tot.map (ev2 M)⟩ := by
    rw [hforms, htot]
    rfl
  refine hs_bind (hs_eqTabsC hz hone hos _) fun L hL ↦ ?_
  refine hs_bind (hs_mapS (fun m : MMemo ↦ ∀ e ∈ m, MOk M (pt.map (ev2 M)) e) (tabConstS z one pt L forms)
      (fun x ↦ (List.range 3).map fun s ↦ constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ))
      (·.map (ev2 M)) (fun m x hm ↦ hs_tabConstS hz hone pt hL forms m hm x) [] _ (by simp)) fun rc hrc ↦
    hs_bind (hs_pure (P := fun cs ↦ cs = rc.2) rfl) fun consts hce ↦ ?_
  have hcs : consts.map (·.map (ev2 M)) = tabs.zipIdx.map fun x ↦ (List.range 3).map fun s ↦
      constG x.1 (evF M (formAt forms x.2 s)) ((pt.map (ev2 M)).take x.1.τ) := by
    rw [hce]
    exact hrc.2
  refine hs_bind (hs_mapB2 (partsC z tabs forms pt) _ (·.map (evP M))
      (fun s ↦ hs_partsC hz tabs forms pt (tot.map (ev2 M)) s) _) fun ps hps ↦ ?_
  refine hs_bind (hs_mapB2m (valC z consts tot) _ (ev2 M) _
      fun s hs ↦ hs_valC hz tabs forms hcs tot (List.mem_range.mp hs)) fun vals hvals ↦ hs_pure ⟨?_, ?_⟩
  · rw [hr]
    exact hps
  · rw [hr]
    exact hvals

end Lvm6.Node.MbC
