-- New for lvm2 S2GT (GT-V): V_S's decision at S2GT (`decideFGX`, GT-L's placeholder name and type): S2GF's
-- decision program (`decideProgFFG`, generic in the public values' reader and the `KS` link's rows) with S2GT's
-- 16-B header scalars, the S2GT trace's continuation rows, T-H1's typed phases at `E2`, and `Φ_Q` at `E2`.
import LvmE2VFast
import LvmE2TV
import LvmE2TSpec
import LvmS2GTSched
import LvmQTypedHarC

/-!
# V_S's decision at S2GT

`decideFGX N vk c sig`: from the cursor after S2GT's header (`headerBytesP P20T`, 5,664 B), `decideProgFFG` with
* the public values `pubOfW fe16At 16 accVT` (`acc_in`: 46 scalars of 16 B, `c₂ = 0`);
* the `KS` link's continuation rows `contRowsT` (the S2GT trace's 4,288 blocks);
* the typed phases `dTypedT P20T N` (zerocheck, wiring, relayout and A23 at `E2`, the mini-bus at `E3`);

read as `decideFFX`: every check held, `Σ` read to its end, and `Φ_Q` at `E2` (`N.phiT`, 45 coordinates) at the
folded accumulator (read back from its `E3` form, `c₂ = 0`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open RecursionFast Lvm

/-- S2GT's public values: `acc_in` of `accVT = 45` coordinates in 16-B scalars. -/
def pubG (vk c : Vector UInt8 32) (sig : ByteArray) : Pub := pubOfW fe16At 16 Lvm.VEq.accVT vk c sig

/-- **A region claim's two weights at S2GT, together** (`affWD`'s `Quad Ext3` sum once, with `wordWDF`): coordinate
`re` and `im` of the region weight. -/
def affPairD (N : TNatT) (s : Lvm.Typed.YSrc) (r : List FE2) : List FE → FE × FE :=
  let terms := (N.toN.regsOf s).map fun g =>
    (FE6.ofE2 (hiWG r g.log g.base), r.take g.log, g.log, g.dst >>> g.log)
  fun X =>
    let acc := terms.foldl (fun (acc : FE6) t =>
      let w := FE6.mul (FE6.mul t.1 (wordWDF t.2.1 (X.take t.2.2.1))) (FE6.ofE (eqAtF (X.drop t.2.2.1) t.2.2.2))
      ⟨acc.re + w.re, acc.im + w.im⟩) ⟨0, 0⟩
    (acc.re, acc.im)

/-- **`affPairD` in a region of the small shape** (stack `nu0`, region `reg`): a term whose block misses the region is
skipped, its `eqAtF` being `0` at the region's points (`Shape.eqAbove_relocF_eq_zero`, `keepPart`). -/
def affPairDR (N : TNatT) (s : Lvm.Typed.YSrc) (r : List FE2) (nu : Nat) :
    Nat → (Nat × Nat × Nat) → List FE → FE × FE :=
  let terms := (N.toN.regsOf s).map fun g =>
    (FE6.ofE2 (hiWG r g.log g.base), r.take g.log, g.log, g.dst)
  fun nu0 reg X =>
    let acc := terms.foldl (fun (acc : FE6) t =>
      if keepPart nu0 nu reg ⟨t.2.2.1, t.2.2.2⟩ then
        let w := FE6.mul (FE6.mul t.1 (wordWDF t.2.1 (X.take t.2.2.1)))
          (FE6.ofE (eqAtF (X.drop t.2.2.1) (t.2.2.2 >>> t.2.2.1)))
        ⟨acc.re + w.re, acc.im + w.im⟩
      else acc) ⟨0, 0⟩
    (acc.re, acc.im)

theorem affPairDR_eq (N : TNatT) (s : Lvm.Typed.YSrc) (r : List FE2) (nu nu0 : Nat) (x : List FE)
    (reg : Nat × Nat × Nat) (hreg : reg ∈ (TypedV.regionsN nu0).filter (Shape.meets ⟨nu, 0⟩)) :
    affPairDR N s r nu nu0 reg ((TypedV.relocN nu0 x reg).take nu) =
      affPairD N s r ((TypedV.relocN nu0 x reg).take nu) := by
  simp only [affPairDR, affPairD, List.foldl_map]
  refine Prod.ext ?_ ?_ <;>
  · first
      | refine congrArg FE6.re (List.foldl_ext _ _ _ fun acc g _ => ?_)
      | refine congrArg FE6.im (List.foldl_ext _ _ _ fun acc g _ => ?_)
    by_cases hk : keepPart nu0 nu reg ⟨g.log, g.dst⟩ = false
    · rw [if_neg (by rw [hk]; exact Bool.false_ne_true)]
      unfold keepPart at hk
      simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨⟨h1, h2⟩, hm⟩, hst⟩ := hk
      subst h1 h2
      have hr23 : reg ∈ Shape.regions := (List.mem_filter.mp hreg).1
      obtain ⟨hk1, -, -⟩ := Shape.regions_facts reg hr23
      have hlen : (TypedV.relocN 23 x reg).length = 23 :=
        Shape.length_relocF x reg (by (clear * - hk1; omega))
      have h0 : eqAtF (((TypedV.relocN 23 x reg).take 23).drop g.log) (g.dst >>> g.log) = 0 := by
        rw [List.take_of_length_le (by omega), ← Lvm.Har.eqAbove_eqAtF]
        exact Shape.eqAbove_relocF_eq_zero ⟨g.log, g.dst⟩ (inStack_of_B hst) x hr23 hm
      obtain ⟨are, aim⟩ := acc
      simp only [h0, FE6.mul, FE6.ofE, FE6.mk.injEq]
      constructor <;> ring
    · simp only [Bool.not_eq_false] at hk
      rw [if_pos hk]

/-- **The typed claims at S2GT as opening items** (`typedClaimsND`'s order): the relayout's split point claim, then
`σ′`'s, the committed block's and the `KS` aliases' region claims, each `E2` claim's halves weighed together. -/
def typedItemsND (N : TNatT) (p : Params) (ry rv rr : List FE2) (vR : FE2) : List FItem :=
  let reg (s : Lvm.Typed.YSrc) (v : FE2) : FItem :=
    .pairR p.nuMain (affPairD N s ry) (affPairDR N s ry p.nuMain)
      (fun nu0 x reg h => affPairDR_eq N s ry p.nuMain nu0 x reg h) (FE.ofK v.re) (FE.ofK v.im) 0 0
  [.split p.nuMain [(1, ⟨p.nuRec, (layout0 p).s⟩, rr)] vR 0 0, reg .sigma (rv.getD 2 0), reg .com (rv.getD 0 0),
    reg .ks (rv.getD 3 0)]

/-- The mini-bus's instance at S2GT: `M3.real` with `PUB`'s check on the 2-lane header (`Pub.hdrLanesT`, A2). -/
def m3G (N : TNatT) (p : Params) : M3 := M3.realW Pub.hdrLanesT p fun _ => N.mbT

/-- **The mini-bus's column claims as items**: one `FItem.tab` per table (its committed columns at the table's point,
`M3.tableClaimsR`'s order). -/
def tabItemsR (tabs : List M3.Tab) (evs : List (List FE × List FE)) : List FItem :=
  (tabs.zip evs).map fun te => FItem.tab te.1.τ te.2.1 (te.1.cols.zipIdx.filterMap fun ci => match ci.1 with
    | .com rec off => some (if rec then .crec else .main, off, te.2.2.getD ci.2 0)
    | .fix _ _ => none)

theorem tabItemsR_flat (tabs : List M3.Tab) (evs : List (List FE × List FE)) :
    (tabItemsR tabs evs).flatMap FItem.flat = Shape.zeroTails (M3.tableClaimsR tabs evs) := by
  unfold tabItemsR M3.tableClaimsR Shape.zeroTails
  generalize tabs.zip evs = l
  induction l with
  | nil => rfl
  | cons te l ih =>
    obtain ⟨t, pt, ev⟩ := te
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    simp only [FItem.flat, List.map_filterMap]
    congr 1
    funext ci
    obtain ⟨c, i⟩ := ci
    cases c <;> rfl

/-- **The decision program at S2GT** (`decideProgFFGM` at `P20T`: the typed claims as items, the mini-bus's claims
one item per table). -/
def decideProgG (N : TNatT) (vk c : Vector UInt8 32) : DM Acc :=
  decideProgFFGM pubG contRowsT P20T (fun m pub => dTypedTG P20 N m pub (typedItemsND N P20)) (m3G N)
    (fun _ evals => tabItemsR (M3.sumcheckTabs N.mbT) evals) vk c

/-- **The items stand for the typed claims**: `typedItemsND` flattens to `typedClaimsND` (the relayout's split by
`splitDF = splitD`, each region pair by `wordWDF = wordWD`). -/
theorem typedItemsND_flat (N : TNatT) (p : Params) (ry rv rr : List FE2) (vR : FE2) :
    (typedItemsND N p ry rv rr vR).flatMap FItem.flat = typedClaimsND N p ry rv rr vR := by
  have hreg : ∀ (s : Lvm.Typed.YSrc) (v : FE2),
      FItem.flat (.pairR p.nuMain (affPairD N s ry) (affPairDR N s ry p.nuMain)
        (fun nu0 x reg h => affPairDR_eq N s ry p.nuMain nu0 x reg h) (FE.ofK v.re) (FE.ofK v.im) 0 0) =
        regClaimsND N p s ry v := by
    intro s v
    have h0 : (fun y => (affPairD N s ry y).1) = affWD N s ry false := by
      funext X; simp only [affPairD, affWD, wordWDF_eq, if_false, Bool.false_eq_true]
    have h1 : (fun y => (affPairD N s ry y).2) = affWD N s ry true := by
      funext X; simp only [affPairD, affWD, wordWDF_eq, if_true]
    simp only [FItem.flat, regClaimsND, List.map_cons, List.map_nil, h0, h1, if_true, if_false,
      Bool.false_eq_true]
  have hs : FItem.flat (.split p.nuMain [(1, ⟨p.nuRec, (layout0 p).s⟩, rr)] vR 0 0) =
      splitZ p.nuMain [(1, ⟨p.nuRec, (layout0 p).s⟩, rr)] vR := by
    rw [← splitZF_eq]; rfl
  unfold typedItemsND typedClaimsND
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    hreg, hreg, hreg, hs]
  simp only [List.append_assoc]

/-- The typed phases' items flatten to `dTypedT`'s claims. -/
theorem flatI_typedT (N : TNatT) :
    flatI (fun m pub => dTypedTG P20 N m pub (typedItemsND N P20)) = fun m pub => dTypedT P20 N m pub := by
  funext m pub
  unfold flatI dTypedT dTypedTG
  simp only [map_bind, map_pure, typedItemsND_flat]

/-- **V_S's S2GT decision program is `decideProgFG`'s instance** (the fast twins out: `decideProgFFGM_eq`). -/
theorem decideProgG_eq (N : TNatT) (vk c : Vector UInt8 32) :
    decideProgG N vk c = decideProgFG pubG contRowsT P20T (fun m pub => dTypedT P20 N m pub) (m3G N) vk c := by
  unfold decideProgG
  rw [decideProgFFGM_eq _ _ _ _ _ _ (fun _ evals => tabItemsR_flat _ evals), flatI_typedT]

/-- **V_S's decision at S2GT** on the stream `sig` for the native record `N`. -/
def decideFGX (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := DM.runOnH (headerBytesP P20T) (decideProgG N vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phiT (a.pt.map Lvm.e2OfFE) == Lvm.e2OfFE a.y

end Lvm.E2T
