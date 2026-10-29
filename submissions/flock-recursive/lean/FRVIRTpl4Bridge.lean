-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, B-13, A.11; stage S-E12e, track L-circ).
import FRNodeRows4
import FRSegTarget4
import FRVerifierImplNode4

/-!
# The 4.1 `shiftMask` templates against the 4.1 ops, and the prototypes' soundness at one kind

The templates (`FRVIRTplSeg`, `FRVIRTplMaskN`) sit upstream of the ops they mirror, so they are
stated against copies. Here the copies are the ops:

* **`segMaskV_eq`**: `segMaskV = shiftSegI` (`FRSegTarget4`; by `rfl`);
* **`maskNV_eq`**: `maskNV (maskQ ν) = shiftMask4I ν` (`FRVerifierImplNode4`);
* **`routeOk_implSeg`**, **`routeOk_implN4`**: the segment's `implSeg` meets prototype 1's route at
  every kind; the node's `implN4 … (nodeOf ι)` meets prototype 0's at index `ι` (and, the kinds'
  masks differing, not at another index: `routeOk_implN4_ctl`);
* **`protoCS_soundAt`**: `compileTF4_soundAt` at prototype `π` (its set, route, layout, selector
  forms, base and program).
-/

namespace FR
namespace Rev4
open Circ Tpl RecursionFast

/-! ## The copies are the ops -/

theorem lastAtV_eq : lastAtV = lastAt := rfl

/-- **The segment template's value is `shiftSegI`.** -/
theorem segMaskV_eq : segMaskV = shiftSegI := rfl

theorem mFV_eq {n : ℕ} : @mFV n = @NI4.mF n := rfl

theorem shPV_eq : ∀ (n : ℕ) (m : Fin n → Bool → Bool → F) (c : ℕ), shPV n m c = NI4.shP n m c
  | 0, _, _ => rfl
  | n + 1, m, c => by rw [shPV, NI4.shP, shPV_eq n]

/-- **The node template's value at a kind's constants is `shiftMask4I`** (both meet `shiftMask4S`:
`maskNV` mirrors S-CN4's first computed form, `prefixP`/`shP`; S-CN4b's `shiftMask4I` reads the
factors from a table). -/
theorem maskNV_eq (ν : NodeKind) : maskNV (maskQ ν) = NI4.shiftMask4I ν := by
  funext τ r
  rw [NI4.shiftMask4_meets, show maskQ ν = (NT4.nbN ν, N4c.chLen ν 0, N4c.chLen ν 1) from rfl]
  obtain ⟨h1, h2, h3, h4⟩ := NT4.chLen_facts ν
  have hw : N4c.wotsB ν 0 < N4c.hUsedN ν := by
    have := NT4.wotsB_hUsed ν (σ := 0) (by norm_num); omega
  simp only [maskNV, NT4.shiftMask4S, NT4.lkE, NT4.lkSh, NT4.lkE0, shPV_eq, mFV_eq]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only
  · rw [NI4.sum_lk ν, prefixP_eq]
    simp only [NI4.prod_mF]
  · rw [NI4.sum_lk ν, NI4.shP_eq, show N4c.chLen ν 0 - 1 + 1 = N4c.chLen ν 0 by omega]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [NI4.prod_mF]
    by_cases hx : x.val < N4c.chLen ν 0 + N4c.chLen ν 1 - 1
    · rw [if_pos ⟨hx, by omega⟩, if_pos hx]
    · rw [if_neg (fun h => hx h.1), if_neg hx]

/-! ## The routes -/

theorem routeOk_seg {impl : OpImpl} (h : impl.shiftMask = shiftSegI) (κ : Kind) :
    RouteOk (protoR 1) impl κ := by
  show impl.shiftMask = segMaskV
  rw [h, segMaskV_eq]

theorem protoR0 : protoR 0 = .node (Circ.kinds.map fun ι => maskQ (nodeOf ι)) := rfl

theorem routeOk_node {impl : OpImpl} (ι : Kind) (h : impl.shiftMask = NI4.shiftMask4I (nodeOf ι)) :
    RouteOk (protoR 0) impl ι := by
  rw [protoR0]
  refine ⟨by cases ι <;> simp [Circ.kinds, kIx], ?_⟩
  rw [h, ← maskNV_eq]
  cases ι <;> simp [Circ.kinds, kIx]

/-- **The segment's ops meet prototype 1's route** (at every kind). -/
theorem routeOk_implSeg (impl₀ : OpImpl) (κ : Kind) : RouteOk (protoR 1) (implSeg impl₀) κ :=
  routeOk_seg (impl := implSeg impl₀) rfl κ

/-- **The node kind `nodeOf ι`'s ops meet prototype 0's route at index `ι`.** -/
theorem routeOk_implN4 (base : NodeKind → OpImpl) (tS : NodeKind → Array F → Array F) (ι : Kind) :
    RouteOk (protoR 0) (NI4.implN4 base tS (nodeOf ι)) ι :=
  routeOk_node (impl := NI4.implN4 base tS (nodeOf ι)) ι rfl

/-- (+/−) At index `P30` (`N2`) prototype 0's route asks `N2`'s mask, so it holds for `N2`'s ops
iff their mask is `N2`'s: the route is kind-indexed, which is why the node prototype is sound at
one kind (`ExtOkAt`), not at every kind. -/
theorem routeOk_implN4_ctl (impl : OpImpl) (sm : Array F → Array F → F × F × F) :
    RouteOk (protoR 0) { impl with shiftMask := sm } .P30 ↔ sm = NI4.shiftMask4I .N2 := by
  rw [protoR0, ← maskNV_eq]
  simp [RouteOk, Circ.kinds, kIx, nodeOf]

/-! ## The prototypes' soundness at one kind -/

/-- **Prototype `π`'s compile is sound at the run's kind `κ`** (`compileTF4_soundAt` at its set,
route, layout, selector forms, base and program): with `ImplTF` (the kind-free template fields)
and the route's `shiftMask` at `κ` (`routeOk_implN4`, `routeOk_implSeg`), the instance rows, the
auxiliary and skeleton imports and the foreign flags give acceptance and every register's value. -/
theorem protoCS_soundAt (π : ℕ) {impl : OpImpl} {κ : Kind} {inp : Input} {tr tr' : Trace} {s : St}
    {w : Asg} (hT : ImplTF (protoF π) impl) (hR : RouteOk (protoR π) impl κ)
    (hP : SelOk w (protoP π) κ) (he : exec impl κ inp (protoProg π).ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (protoCS π).rows, r.Holds w)
    (ht : ∀ r ∈ (protoCS π).tplRows (protoLay π).ctx (protoP π).one, r.Holds w)
    (hx : ∀ a ∈ (protoCS π).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (protoCS π).imp, RepS w ((protoCS π).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (protoCS π).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((protoCS π).slot i) (rd s.regs i) :=
  compileTF4_soundAt hT hR (protoLay π) (baseR π) hP he hr ht hx hi hf

/-- (+) The node route's constants are the group's in selector order: `N4` (18 coordinates, a
segment's chain then a 4-segment aggregate's), `N2` (17), `N8` (two aggregates). -/
theorem protoR_ctl : protoR 0 = .node [(18, 23875, 95500), (17, 23875, 47750), (18, 95500, 95500)] ∧
    protoR 1 = .seg := by
  exact ⟨rfl, rfl⟩

end Rev4
end FR
