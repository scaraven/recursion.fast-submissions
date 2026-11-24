-- New for lvm6 (WP CC8, second slice). The level-0 weight cell of `wFinG` (NODE §6a (i)): the
-- λ₀-batch of the stack claims' weights at the WHIR point (`w₀ cl`, rotated: the level-0 rounds'
-- challenges are the stack index's top six bits), from one weight gadget per claim; with the
-- gadgets of the `eq`-point claims (FORMAT6 §6.5's tree claims 2–14) and of the ring claims (CC-7).
import Lvm6QCFinV
import Lvm6QCRing
import Lvm6WhirProg

/-!
# The level-0 weight cell (CC8)

**Statements** (Category A, CC8):
* `ClaimAt Pre cl G`: on memories with `Pre`, `G x` is the claim's weight `cl.1` at the cells `x`.
* **`WBatchStmt G`** (CC-8b): for claims `cs` with weight gadgets `Gs` (`ClaimAt`, one each), a cell
  holding `λ₀`, and the batch affine in its 25 variables (W1's `whirSpec18` hypothesis), `G Gs lc`
  meets `WAt Pre (w₀ (batch λ₀ cs))`.

**Gadgets and proofs**: `wBatchG` (one call per claim gadget at the point `τ ++ α₀`, then Horner at
`λ₀`, CC-6b's form), **`wBatchHar`** (W1's `w₀` reads its point through `pad25`; `WAt` asks only at `τ`
of `w₀`'s 19 variables, where `pad25 (α₀ ++ τ)` is the point itself: `pad25_self`, `MA_ofFn_getD`);
`eqPtG`/`eqClaimG`, **`eqClaim_ok`** (`(eqPt a ·, v)`, the claim's point as cells); `ringClaimG`,
**`ringClaim_ok`** (`ringClaim μ r sv [] f g`, CC-7's gadget).
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK

variable {c : Ctx} {M : Mem}

/-! ## Statements -/

/-- **A claim's weight gadget** on memories with `Pre`: at the cells `x`, the weight `cl.1`. -/
def ClaimAt (Pre : Mem → Prop) (cl : Ring.Claim) (G : List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem), Pre M → ∀ (x : List C2) (gate : Cell), gate.val M = 1 →
    HsA c M (G x gate) fun o ↦ ev2 M o = cl.1 (x.map (ev2 M))

/-- **CC-8b, the level-0 weight cell** (statement). -/
def WBatchStmt (G : List (List C2 → Cell → BM C2) → C2 → List RndC → List C2 → Cell → BM C2) :
    Prop :=
  ∀ (cs : List Ring.Claim) (Gs : List (List C2 → Cell → BM C2)) (lam : E2) (lc : C2)
    (Pre : Mem → Prop), List.Forall₂ (fun G cl ↦ ClaimAt Pre cl G) Gs cs →
    (∀ M, Pre M → ev2 M lc = lam) →
    Whir.MA 25 (fun y ↦ (Ring.batch lam cs).1 (y.drop 6 ++ y.take 6)) →
    WAt Pre (Whir.w₀ (Ring.batch lam cs)) (G Gs lc)

/-! ## The batch -/

/-- **The level-0 weight cell**: each claim's gadget at the point `τ ++ α₀` (W1's `w₀` rotation),
then Horner at `λ₀`. -/
def wBatchG (Gs : List (List C2 → Cell → BM C2)) (lc : C2) (rc : List RndC) (τ : List C2)
    (gate : Cell) : BM C2 :=
  mapB (fun G ↦ G (τ ++ rc.map (·.α)) gate) Gs >>= fun ws ↦ g2Zero lc >>= fun z ↦ hornerG z lc ws

theorem hsA_mapClaims {Pre : Mem → Prop} (hP : Pre M) (x : List C2) {gate : Cell}
    (hg : gate.val M = 1) : ∀ {Gs : List (List C2 → Cell → BM C2)} {cs : List Ring.Claim},
    List.Forall₂ (fun G cl ↦ ClaimAt Pre cl G) Gs cs →
    HsA c M (mapB (fun G ↦ G x gate) Gs) fun ws ↦ ws.map (ev2 M) = cs.map fun cl ↦ cl.1 (x.map (ev2 M))
  | [], [], _ => hsA_pure rfl
  | _ :: _, _ :: _, List.Forall₂.cons h1 h2 =>
    hsA_bind (h1 c M hP x gate hg) fun w hw ↦ hsA_bind (hsA_mapClaims hP x hg h2) fun ws hws ↦
      hsA_pure (by rw [List.map_cons, List.map_cons, hw, hws])

/-- A table affine in its first `n` variables stays so when read on the first `n` entries, zero-padded. -/
theorem MA_ofFn_getD : ∀ (n : ℕ) (f : List E2 → E2), Whir.MA n f →
    Whir.MA n fun y ↦ f (List.ofFn fun i : Fin n ↦ y.getD i 0)
  | 0, _, _ => trivial
  | n + 1, f, h => by
    have hc : ∀ (X : E2) (x : List E2), (List.ofFn fun i : Fin (n + 1) ↦ (X :: x).getD i 0) =
        X :: List.ofFn fun i : Fin n ↦ x.getD i 0 := fun X x ↦ by simp [List.ofFn_succ]
    refine ⟨fun X x ↦ ?_, fun X ↦ ?_⟩
    · simp only [hc]
      exact h.1 X _
    · simp only [hc]
      exact MA_ofFn_getD n (fun y ↦ f (X :: y)) (h.2 X)

/-- `pad25` is the identity on lists of length 25. -/
theorem pad25_self {y : List E2} (hy : y.length = 25) : Whir.pad25 y = y :=
  List.ext_getElem (by simp [Whir.pad25, hy]) fun i h1 h2 ↦ by
    simp only [Whir.pad25, List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ h2]

/-- **CC-8b proved** (INT3: on W1's padded `w₀`, at points of `w₀`'s 19 variables). -/
theorem wBatchHar : WBatchStmt wBatchG := by
  intro cs Gs lam lc Pre hGs hlc hma c M hP rc rs hr hl τ hτ gate hgate
  unfold wBatchG
  refine hsA_bind (hsA_mapClaims hP _ hgate hGs) fun ws hws ↦
    hsA_bind (hsA_of_hs (hs_g2Zero lc)) fun z hz ↦ hsA_of_hs (hs_mono (hs_hornerG hz lc ws)
      fun o ho ↦ ?_)
  have hα : (rs.map (·.α)).length = 6 := by rw [List.length_map, hl]
  have hma' : Whir.MA ((rs.map (·.α)).length + 19) (Whir.w₀ (Ring.batch lam cs)).2 := by
    rw [hα]
    exact MA_ofFn_getD 25 _ hma
  rw [wFolds_snd 6 rs _ hl, foldsT_MA _ _ 19 hma']
  have hτ' : τ.length = 19 := hτ
  have hpad : Whir.pad25 ((rs.map (·.α)) ++ τ.map (ev2 M)) = (rs.map (·.α)) ++ τ.map (ev2 M) :=
    pad25_self (by rw [List.length_append, hα, List.length_map, hτ'])
  show ev2 M o = (Ring.batch lam cs).1 ((Whir.pad25 ((rs.map (·.α)) ++ τ.map (ev2 M))).drop 6 ++
    (Whir.pad25 ((rs.map (·.α)) ++ τ.map (ev2 M))).take 6)
  rw [hpad, List.drop_left' hα, List.take_left' hα]
  have hx : (τ ++ rc.map (·.α)).map (ev2 M) = τ.map (ev2 M) ++ rs.map (·.α) := by
    rw [List.map_append, rndsRep_alpha hr]
  have hd := dotF_powersF lam (cs.map fun cl ↦ cl.1 (τ.map (ev2 M) ++ rs.map (·.α)))
  rw [List.length_map] at hd
  show ev2 M o = dotF (powersF lam cs.length) (cs.map fun cl ↦ cl.1 (τ.map (ev2 M) ++ rs.map (·.α)))
  rw [hd, ← hx, ← hws, ← hlc M hP]
  show FE2.toE2 (o.val M) = _
  rw [ho, toE2_polyEvalF, List.map_map]
  rfl

/-! ## The `eq`-point claims -/

/-- `∏ (1 + a_i + x_i)` over the shorter of the two lists (`eqPt`, characteristic 2). -/
def eqPtG (z one : C2) : List C2 → List C2 → BM C2
  | ai :: a, xi :: x => g2Add ai xi >>= fun s ↦ g2Add one s >>= fun f ↦ eqPtG z one a x >>= fun p ↦
      g2Mul f p z
  | _, _ => pure one

theorem hs_eqPtG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) : ∀ a x : List C2,
    Hs c M (eqPtG z one a x) fun r ↦ ev2 M r = eqPt (a.map (ev2 M)) (x.map (ev2 M))
  | [], _ => hs_pure (by simp [eqPt, hone])
  | _ :: _, [] => hs_pure (by simp [eqPt, hone])
  | ai :: a, xi :: x => hs_bind (hs_g2Add ai xi) fun s hs ↦ hs_bind (hs_g2Add one s) fun f hf ↦
    hs_bind (hs_eqPtG hz hone a x) fun p hp ↦ hs_mono (hs_g2Mul f p z) fun r hr ↦ by
      rw [ev2_mul hr, ev2_of_zero hz, add_zero, ev2_add hf, ev2_add hs, hone, hp]
      simp only [eqPt, List.map_cons, List.zipWith_cons_cons, List.prod_cons]
      linear_combination (-(ev2 M ai * ev2 M xi) *
        (List.zipWith (fun r t ↦ r * t + (1 + r) * (1 + t)) (a.map (ev2 M)) (x.map (ev2 M))).prod) *
          two_E2

/-- **An `eq`-point claim's gadget** (one instance per claim; the point `a` as cells). -/
def eqClaimG (a : List C2) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ eqPtG z one a x

/-- **`ClaimAt` for an `eq`-point claim** whose point the cells `a` hold on `Pre`. -/
theorem eqClaim_ok (Pre : Mem → Prop) (a : List C2) (al : List E2) (v : E2)
    (ha : ∀ M, Pre M → a.map (ev2 M) = al) :
    ClaimAt Pre ((fun pt ↦ eqPt al pt), v) (eqClaimG a) := by
  intro c M hP x gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_mono (hs_eqPtG hz (ev2_one' hone) a x) fun r hr ↦ ?_)
  rw [hr, ha M hP]

/-! ## The ring claims -/

/-- **A ring claim's gadget**: CC-7's `ring_weight` at the point's first `μ` coordinates. -/
def ringClaimG (μ : ℕ) (r f g : List C2) (x : List C2) (gate : Cell) : BM C2 :=
  ringWeightGen r (x.take μ) f g gate

/-- **`ClaimAt` for a ring claim** (`ringOf`'s form, no selector): the point and the maps as cells. -/
theorem ringClaim_ok (Pre : Mem → Prop) (μ : ℕ) (r f g : List C2) (rv sv fv gv : List E2)
    (hr : ∀ M, Pre M → r.map (ev2 M) = rv ∧ f.map (ev2 M) = fv ∧ g.map (ev2 M) = gv) :
    ClaimAt Pre (Ring.ringClaim μ rv sv [] fv gv) (ringClaimG μ r f g) := by
  intro c M hP x gate hg
  refine hsA_mono (ringWeightHar c M r (x.take μ) f g gate hg) fun o ho ↦ ?_
  obtain ⟨h1, h2, h3⟩ := hr M hP
  rw [ho, h1, h2, h3, List.map_take]
  simp [Ring.ringClaim, eqEvalF]

end Lvm6.QC
