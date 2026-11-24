-- New for lvm6 (WP CC). Generators and HARs of ring switching's arithmetic in the node circuit:
-- the batched stack claim's value (`ring_target`, then the claims by the powers of `λ₀`, at most
-- `J₀` claims) and the ring claim's weight at a point (`ring_weight` of `ring_coefficients`), as
-- `E2` gadgets (CC-6, CC-7 of `Lvm6QCStmt`).
import Lvm6QCStmt
import LvmE2QWKitSem

/-!
# Ring switching's arithmetic (generator and HAR)

Each gadget transcribes RS's verifier function over `FE2` (the twin of `Lvm6RingMap`), operation
for operation; RS's `toE2_ringTarget`, `toE2_ringCoefficients`, `toE2_ringWeight` carry the value
to `E2`.

* `sqN z v n`: `n` squarings (`frobenius8 v p` is `8p` of them); `psiG`: `ring_psi`'s fold;
  `hornerG`: `polyEvalF` (Horner, lowest coefficient last); `tgtLoop`, `tgtG`: `ring_target`.
* **`ringValGen`**, **`ringValHar : RingValStmt ringValGen`**: `ring_target` then Horner at `λ₀`
  over the claim values (`dotF_powersF`: `dotF (powers(λ, n)) l = polyEvalF l λ` for `|l| = n`).
  About `8·(8 + 64 + 28 + 1) + 64·16 ≈ 1,840` products for the target, `|vs| + 1` for the batch.
* **`ringTargetGen`**, **`batchGen`** (CC-6a/b): the two halves alone, for a batch in FORMAT6 §6.5's
  claim order.
* `coefG`, `prodG`, `wG`; **`ringWeightGen`**, **`ringWeightHar : RingWeightStmt ringWeightGen`**:
  `64` coefficients (`64` products, `512` squarings), then `64·(3|r| + |r|)` operations.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6.Ring (frobenius8 ringPsi ringTarget ringMapWidth ringCoefficients ringWeight)

variable {c : Ctx} {M : Mem}

/-! ## Pure facts -/

theorem foldl_range_succ {α : Type} (f : α → ℕ → α) (a : α) (n : ℕ) :
    (List.range (n + 1)).foldl f a = f ((List.range n).foldl f a) n := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem foldl_add_eq {F : Type} [AddCommMonoid F] : ∀ (a : F) (l : List F),
    l.foldl (· + ·) a = a + l.sum
  | a, [] => by simp
  | a, x :: l => by rw [List.foldl_cons, foldl_add_eq, List.sum_cons, add_assoc]

theorem dotF_eq_sum {F : Type} [Field F] (l r : List F) : dotF l r = (List.zipWith (· * ·) l r).sum := by
  rw [dotF, foldl_add_eq, zero_add]

theorem polyEvalF_cons {F : Type} [Field F] (x : F) (l : List F) (b : F) :
    polyEvalF (x :: l) b = polyEvalF l b * b + x := rfl

theorem dotF_powersFromF {F : Type} [Field F] (b : F) : ∀ (acc : F) (l : List F),
    dotF (powersFromF acc b l.length) l = acc * polyEvalF l b
  | acc, [] => by simp [dotF, powersFromF, polyEvalF]
  | acc, x :: xs => by
    have ih := dotF_powersFromF b (acc * b) xs
    rw [dotF_eq_sum] at ih ⊢
    rw [List.length_cons, powersFromF, List.zipWith_cons_cons, List.sum_cons, ih, polyEvalF_cons]
    ring

/-- **The batch is Horner's rule at `λ`**: `dotF (powers(λ, |l|)) l = polyEvalF l λ`. -/
theorem dotF_powersF {F : Type} [Field F] (b : F) (l : List F) :
    dotF (powersF b l.length) l = polyEvalF l b := by
  rw [powersF, dotF_powersFromF, one_mul]

theorem map_polyEvalF' {F G : Type} [Field F] [Field G] (φ : F →+* G) (x : F) :
    ∀ l : List F, φ (polyEvalF l x) = polyEvalF (l.map φ) (φ x)
  | [] => by simp [polyEvalF]
  | a :: l => by
    rw [polyEvalF_cons, List.map_cons, polyEvalF_cons, map_add, map_mul, map_polyEvalF' φ x l]

theorem toE2_polyEvalF (l : List FE2) (x : FE2) :
    FE2.toE2 (polyEvalF l x) = polyEvalF (l.map FE2.toE2) (FE2.toE2 x) := by
  rw [show (FE2.toE2 : FE2 → E2) = ⇑FE2.ringEquivE2 from rfl]
  exact map_polyEvalF' FE2.ringEquivE2.toRingHom x l

theorem map_ev2 (l : List C2) : l.map (ev2 M) = (l.map (C2.val M)).map FE2.toE2 := by
  rw [List.map_map]
  rfl

/-! ## Squarings, `ring_psi`, Horner -/

/-- `n` squarings of `v` (`z` a zero). -/
def sqN (z v : C2) : ℕ → BM C2
  | 0 => pure v
  | n + 1 => sqN z v n >>= fun r ↦ g2Mul r r z

theorem hs_sqN {z : C2} (hz : z.val M = 0) (v : C2) : ∀ n,
    Hs c M (sqN z v n) fun r ↦ r.val M = (List.range n).foldl (fun x _ ↦ x * x) (v.val M)
  | 0 => hs_pure rfl
  | n + 1 => hs_bind (hs_sqN hz v n) fun r hr ↦ hs_mono (hs_g2Mul r r z) fun s hs ↦ by
    rw [hs, hz, add_zero, hr, foldl_range_succ]

theorem hs_frob {z : C2} (hz : z.val M = 0) (v : C2) (p : ℕ) :
    Hs c M (sqN z v (8 * p)) fun r ↦ r.val M = frobenius8 (v.val M) p :=
  hs_sqN hz v (8 * p)

/-- `ring_psi`'s fold from the accumulator `(a₁, a₂)`. -/
def psiG (z : C2) : C2 → C2 → List C2 → BM (C2 × C2)
  | a1, a2, [] => pure (a1, a2)
  | a1, a2, gb :: gs => g2Mul gb a2 a1 >>= fun a1' ↦ g2Mul a2 a2 z >>= fun a2' ↦ psiG z a1' a2' gs

theorem hs_psiG {z : C2} (hz : z.val M = 0) : ∀ (a1 a2 : C2) (gs : List C2),
    Hs c M (psiG z a1 a2 gs) fun r ↦ (r.1.val M, r.2.val M) = (gs.map (C2.val M)).foldl
      (fun (acc : FE2 × FE2) gb ↦ (acc.1 + gb * acc.2, acc.2 * acc.2)) (a1.val M, a2.val M)
  | a1, a2, [] => hs_pure rfl
  | a1, a2, gb :: gs => hs_bind (hs_g2Mul gb a2 a1) fun a1' h1 ↦ hs_bind (hs_g2Mul a2 a2 z)
    fun a2' h2 ↦ hs_mono (hs_psiG hz a1' a2' gs) fun r hr ↦ by
      rw [hr, h1, h2, hz, add_zero, add_comm (gb.val M * a2.val M)]
      rfl

theorem hs_psi {z : C2} (hz : z.val M = 0) (gs : List C2) (s : C2) :
    Hs c M (psiG z z s gs >>= fun r ↦ pure r.1) fun r ↦
      r.val M = ringPsi (s.val M) (gs.map (C2.val M)) :=
  hs_bind (hs_psiG hz z s gs) fun r hr ↦ hs_pure (by
    have := congrArg Prod.fst hr
    simp only [hz] at this
    exact this)

/-- Horner's rule at `pt` (`polyEvalF`, lowest coefficient first in the list). -/
def hornerG (z pt : C2) : List C2 → BM C2
  | [] => pure z
  | x :: xs => hornerG z pt xs >>= fun acc ↦ g2Mul acc pt x

theorem hs_hornerG {z : C2} (hz : z.val M = 0) (pt : C2) : ∀ l : List C2,
    Hs c M (hornerG z pt l) fun r ↦ r.val M = polyEvalF (l.map (C2.val M)) (pt.val M)
  | [] => hs_pure (by rw [hz]; rfl)
  | x :: xs => hs_bind (hs_hornerG hz pt xs) fun acc h ↦ hs_mono (hs_g2Mul acc pt x) fun r hr ↦ by
    rw [hr, h, List.map_cons, polyEvalF_cons]

/-! ## `ring_target` -/

/-- `ring_target`'s loop over `p` (`p` from `7` down), from the accumulator `(a₁, a₂)`. -/
def tgtLoop (z : C2) (fs imgs : List C2) : List ℕ → C2 → C2 → BM C2
  | [], a1, _ => pure a1
  | p :: ps, a1, a2 => sqN z a2 8 >>= fun zz ↦ hornerG z zz imgs >>= fun e ↦
      sqN z e (8 * p) >>= fun fe ↦ g2Mul (fs.getD p z) fe a1 >>= fun a1' ↦ tgtLoop z fs imgs ps a1' zz

theorem getD_val {z : C2} (hz : z.val M = 0) (fs : List C2) (p : ℕ) :
    (fs.map (C2.val M)).getD p 0 = (fs.getD p z).val M := by
  rw [← hz, List.getD_map]

theorem hs_tgtLoop {z : C2} (hz : z.val M = 0) (fs imgs : List C2) : ∀ (ps : List ℕ) (a1 a2 : C2),
    Hs c M (tgtLoop z fs imgs ps a1 a2) fun r ↦ r.val M = (ps.foldl (fun (acc : FE2 × FE2) p ↦
      let zz := frobenius8 acc.2 1
      (acc.1 + (fs.map (C2.val M)).getD p 0 * frobenius8 (polyEvalF (imgs.map (C2.val M)) zz) p, zz))
        (a1.val M, a2.val M)).1
  | [], a1, _ => hs_pure rfl
  | p :: ps, a1, a2 => hs_bind (hs_frob hz a2 1) fun zz hzz ↦ hs_bind (hs_hornerG hz zz imgs)
    fun e he ↦ hs_bind (hs_frob hz e p) fun fe hfe ↦ hs_bind (hs_g2Mul (fs.getD p z) fe a1)
    fun a1' h1 ↦ hs_mono (hs_tgtLoop hz fs imgs ps a1' zz) fun r hr ↦ by
      rw [hr, h1, hfe, he, hzz, ← getD_val hz, List.foldl_cons, add_comm]

/-- **`ring_target`** (`x` the constant `GEN`). -/
def tgtG (z x : C2) (sv fs gs : List C2) : BM C2 :=
  mapB (fun s ↦ psiG z z s gs >>= fun r ↦ pure r.1) sv >>= fun imgs ↦
    tgtLoop z fs imgs [7, 6, 5, 4, 3, 2, 1, 0] z x

theorem hs_tgtG {z x : C2} (hz : z.val M = 0) (hx : x.val M = FE2.ofK FK.x) (sv fs gs : List C2) :
    Hs c M (tgtG z x sv fs gs) fun r ↦ r.val M =
      ringTarget (FE2.ofK FK.x) (sv.map (C2.val M)) (fs.map (C2.val M)) (gs.map (C2.val M)) :=
  hs_bind (hs_mapB _ (fun s ↦ ringPsi (s.val M) (gs.map (C2.val M))) (hs_psi hz gs) sv)
    fun imgs himgs ↦ hs_mono (hs_tgtLoop hz fs imgs _ z x) fun r hr ↦ by
      rw [hr, himgs, hz, hx, ringTarget, List.map_map]
      rfl

/-! ## CC-6: the batched claim's value -/

/-- **The batched claim's value**: `ring_target` (the constant `x` and a zero from `λ₀`'s cells),
then Horner at `λ₀` over `ring_target :: vs`. -/
def ringValGen (sv f g : List C2) (lam : C2) (vs : List C2) (_gate : Cell) : BM C2 :=
  g2Zero lam >>= fun z ↦ g2Const (FE2.ofK FK.x) lam >>= fun x ↦ tgtG z x sv f g >>= fun t ↦
    hornerG z lam (t :: vs)

/-- **CC-6 proved.** -/
theorem ringValHar : RingValStmt ringValGen := by
  intro c M sv f g lam vs gate _ _
  refine hsA_of_hs (hs_bind (hs_g2Zero lam) fun z hz ↦ hs_bind (hs_g2Const (FE2.ofK FK.x) lam)
    fun x hx ↦ hs_bind (hs_tgtG hz hx sv f g) fun t ht ↦ hs_mono (hs_hornerG hz lam (t :: vs))
    fun o ho μ r off cs hcs ↦ ?_)
  have hT : ev2 M t = ringTarget Ring.genE2 (sv.map (ev2 M)) (f.map (ev2 M)) (g.map (ev2 M)) := by
    rw [ev2, ht, Ring.toE2_ringTarget, map_ev2, map_ev2, map_ev2]
  have hlen : cs.length = vs.length := by simpa using congrArg List.length hcs
  simp only [Ring.stackClaim, Ring.batch, Ring.ringClaim, List.map_cons, List.length_cons]
  rw [hcs, ← hT, hlen, show vs.length + 1 = (ev2 M t :: vs.map (ev2 M)).length by simp,
    dotF_powersF]
  show FE2.toE2 (o.val M) = _
  rw [ho, toE2_polyEvalF, ← map_ev2]
  rfl

/-- **`ring_target` alone** (a zero and the constant `GEN` from any cell). -/
def ringTargetGen (sv f g : List C2) (_gate : Cell) : BM C2 :=
  g2Zero default >>= fun z ↦ g2Const (FE2.ofK FK.x) default >>= fun x ↦ tgtG z x sv f g

/-- **CC-6a proved.** -/
theorem ringTargetHar : RingTargetStmt ringTargetGen := by
  intro c M sv f g gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero default) fun z hz ↦ hs_bind (hs_g2Const (FE2.ofK FK.x) default)
    fun x hx ↦ hs_mono (hs_tgtG hz hx sv f g) fun o ho ↦ ?_)
  rw [ev2, ho, Ring.toE2_ringTarget, map_ev2, map_ev2, map_ev2]

/-- **The batch alone**: Horner at `λ` over the values (a zero from `λ`'s cells). -/
def batchGen (lam : C2) (vs : List C2) (_gate : Cell) : BM C2 :=
  g2Zero lam >>= fun z ↦ hornerG z lam vs

/-- **CC-6b proved.** -/
theorem batchHar : BatchValStmt batchGen := by
  intro c M lam vs gate _ _
  refine hsA_of_hs (hs_bind (hs_g2Zero lam) fun z hz ↦ hs_mono (hs_hornerG hz lam vs) fun o ho ↦ ?_)
  rw [← List.length_map (f := ev2 M) (as := vs), dotF_powersF]
  show FE2.toE2 (o.val M) = _
  rw [ho, toE2_polyEvalF, ← map_ev2]
  rfl

/-! ## CC-7: the ring claim's weight -/

/-- `ring_coefficients`' fold from the accumulator `(a₁, a₂)`: block after block. -/
def coefG (z : C2) : List C2 → List C2 → List C2 → BM (List C2 × List C2)
  | a1, a2, [] => pure (a1, a2)
  | a1, a2, fp :: fs => mapB (fun gb ↦ g2Mul fp gb z) a2 >>= fun prods ↦
      mapB (fun gb ↦ sqN z gb (8 * 1)) a2 >>= fun a2' ↦ coefG z (a1 ++ prods) a2' fs

theorem hs_coefG {z : C2} (hz : z.val M = 0) : ∀ (fs a1 a2 : List C2),
    Hs c M (coefG z a1 a2 fs) fun r ↦ (r.1.map (C2.val M), r.2.map (C2.val M)) =
      (fs.map (C2.val M)).foldl (fun (acc : List FE2 × List FE2) fp ↦
        (acc.1 ++ acc.2.map (fp * ·), acc.2.map (frobenius8 · 1))) (a1.map (C2.val M), a2.map (C2.val M)) := by
  intro fs
  induction fs with
  | nil => intro a1 a2; exact hs_pure rfl
  | cons fp fs ih =>
    intro a1 a2
    show Hs c M (mapB (fun gb ↦ g2Mul fp gb z) a2 >>= fun prods ↦
      mapB (fun gb ↦ sqN z gb (8 * 1)) a2 >>= fun a2' ↦ coefG z (a1 ++ prods) a2' fs) _
    have hm : ∀ gb : C2, Hs c M (g2Mul fp gb z) fun r ↦ r.val M = fp.val M * gb.val M := fun gb ↦
      hs_mono (hs_g2Mul fp gb z) fun r hr ↦ by rw [hr, hz, add_zero]
    refine hs_bind (hs_mapB (fun gb ↦ g2Mul fp gb z) (fun gb ↦ fp.val M * gb.val M) hm a2)
      fun prods hp ↦ ?_
    refine hs_bind (hs_mapB (fun gb ↦ sqN z gb (8 * 1)) (fun gb ↦ frobenius8 (gb.val M) 1)
      (fun gb ↦ hs_frob hz gb 1) a2) fun a2' h2 ↦ ?_
    refine hs_mono (ih (a1 ++ prods) a2') fun r hr ↦ ?_
    rw [hr, List.map_cons, List.foldl_cons, List.map_append, hp, h2]
    simp only [List.map_map, Function.comp_def]

/-- `Π (1 + a + b)` over the pairs, from `pr`. -/
def prodG (z : C2) : C2 → List (C2 × C2) → BM C2
  | pr, [] => pure pr
  | pr, (a, b) :: ps => g2One a >>= fun a1 ↦ g2Add a1 b >>= fun t ↦ g2Mul pr t z >>= fun pr' ↦
      prodG z pr' ps

theorem hs_prodG {z : C2} (hz : z.val M = 0) : ∀ (pr : C2) (ps : List (C2 × C2)),
    Hs c M (prodG z pr ps) fun r ↦ r.val M = (ps.map fun p ↦ (p.1.val M, p.2.val M)).foldl
      (fun product (p : FE2 × FE2) ↦ product * (1 + p.1 + p.2)) (pr.val M)
  | pr, [] => hs_pure rfl
  | pr, (a, b) :: ps => hs_bind (hs_g2One a) fun a1 h1 ↦ hs_bind (hs_g2Add a1 b) fun t ht ↦
    hs_bind (hs_g2Mul pr t z) fun pr' hp ↦ hs_mono (hs_prodG hz pr' ps) fun r hr ↦ by
      rw [hr, hp, ht, h1, hz, add_zero]
      rfl

/-- `ring_weight`'s fold over the coefficients from the accumulator `(a₁, a₂)`. -/
def wG (z : C2) (r' : List C2) : C2 → List C2 → List C2 → BM C2
  | a1, _, [] => pure a1
  | a1, a2, cc :: cs => prodG z cc (List.zip a2 r') >>= fun pr ↦ g2Add a1 pr >>= fun a1' ↦
      mapB (fun v ↦ g2Mul v v z) a2 >>= fun a2' ↦ wG z r' a1' a2' cs

theorem hs_wG {z : C2} (hz : z.val M = 0) (r' : List C2) : ∀ (a1 : C2) (a2 cs : List C2),
    Hs c M (wG z r' a1 a2 cs) fun r ↦ r.val M = ((cs.map (C2.val M)).foldl
      (fun (acc : FE2 × List FE2) cc ↦
        let product := (List.zip acc.2 (r'.map (C2.val M))).foldl
          (fun product (p : FE2 × FE2) ↦ product * (1 + p.1 + p.2)) cc
        (acc.1 + product, acc.2.map fun value ↦ value * value)) (a1.val M, a2.map (C2.val M))).1
  | a1, _, [] => hs_pure rfl
  | a1, a2, cc :: cs => hs_bind (hs_prodG hz cc (List.zip a2 r')) fun pr hp ↦
    hs_bind (hs_g2Add a1 pr) fun a1' h1 ↦ hs_bind (hs_mapB _ (fun v ↦ v.val M * v.val M)
      (fun v ↦ hs_mono (hs_g2Mul v v z) fun r hr ↦ by rw [hr, hz, add_zero]) a2) fun a2' h2 ↦
      hs_mono (hs_wG hz r' a1' a2' cs) fun r hr ↦ by
        rw [hr, h1, hp, h2, List.map_cons, List.foldl_cons, List.zip_map, List.map_map]
        rfl

/-- **The ring claim's weight**: the coefficients, then the weight (a zero from any cell). -/
def ringWeightGen (r r' f g : List C2) (_gate : Cell) : BM C2 :=
  g2Zero default >>= fun z ↦ coefG z [] g f >>= fun cg ↦ wG z r' z r cg.1

/-- **CC-7 proved.** -/
theorem ringWeightHar : RingWeightStmt ringWeightGen := by
  intro c M r r' f g gate _
  refine hsA_of_hs (hs_bind (hs_g2Zero default) fun z hz ↦ hs_bind (hs_coefG hz f [] g) fun cg hcg ↦
    hs_mono (hs_wG hz r' z r cg.1) fun o ho ↦ ?_)
  have hc : cg.1.map (C2.val M) = ringCoefficients (f.map (C2.val M)) (g.map (C2.val M)) := by
    have := congrArg Prod.fst hcg
    exact this
  rw [ev2, ho, hz, map_ev2, map_ev2, map_ev2, map_ev2, ← Ring.toE2_ringCoefficients, ← hc,
    ← Ring.toE2_ringWeight]
  rfl

end Lvm6.QC
