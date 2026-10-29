-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.11's replay templates; stage S-E14, track
-- L-circ).
import FRNodeRows4Rep

/-!
# The first replay template: a segment slot's `linkWAll`

A segment slot runs its ops at `L32` (`implP … 1 ι = (implSeg impl₀).fixK .L32`), and a leaf kind's
`linkWAll` is `0^8` (`Impl.implCWith`: the WOTS link families exist only in a node). So the replay
of prototype 1's `linkWAll` import is eight rows `one · out_j = 0` on its `af 8` output cells
(**`zeroRows`**; any other output slot gets the rejecting row `one · one = 0`).

* **`rtLinkSeg`** covers `linkWAll`; **`rtSeg π`** is it at prototype 1 and `RT.none` at prototype 0
  (the previous node's `linkWAll` is `linkWAll4I ν`, JOURNAL §1.4).
* **`rtLinkSeg_ok`**: `RTOk` at every index, given that the base's `linkWAll` at `L32` is `0^8`
  (**`LinkZero impl₀`**; `linkZero_implC`: it holds at the submission's `implC`).
* (REPF: `repOk_rtSeg` removed: `RepOk` is now the `RTOkW` form, which `rtLinkSeg`, without its
  output cells' bound check, does not meet; `FRNodeRows4RepN.rtLinkSegW` is its checked form.)
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-- **The segment's `linkWAll` replay.** -/
def rtLinkSeg : RT := ⟨isLinkW, fun P _ op outs => if isLinkW op then zeroRows P outs else []⟩

/-- **The replay templates per prototype**: the segment's `linkWAll` at prototype 1. -/
def rtSeg (π : ℕ) : RT := if π = 1 then rtLinkSeg else RT.none

/-- The base reads a leaf kind's `linkWAll` as `0^8`. -/
def LinkZero (impl₀ : OpImpl) : Prop := ∀ tt rr, impl₀.linkWAll .L32 tt rr = Array.replicate nLinkFam 0

theorem linkZero_implC (fin : Finals) (lRows : List Row) (κs₀ : F) : LinkZero (Impl.implC fin lRows κs₀) :=
  fun _ _ => rfl

/-- The rejecting row does not hold where `one = 1`. -/
theorem rej_not {P : Params} {w : Asg} (hone : P.one.ev w = 1) : ¬ (⟨P.one, P.one, []⟩ : Row).Holds w := by
  simp [Row.Holds, hone]

/-- **`zeroRows` gives `0^8`**: where they hold (with `one = 1`), the slot list represents
`[af 0^8]`. -/
theorem zeroRows_sound {P : Params} {w : Asg} (hone : P.one.ev w = 1) {outs : List Slot}
    (h : ∀ r ∈ zeroRows P outs, r.Holds w) :
    List.Forall₂ (RepS w) outs [.af (Array.replicate nLinkFam 0)] := by
  have rej : ∀ {l : List Row}, (⟨P.one, P.one, []⟩ : Row) ∈ l → (∀ r ∈ l, r.Holds w) → False :=
    fun hm h' => rej_not hone (h' _ hm)
  match outs, h with
  | [some (t, ls)], h =>
    by_cases hl : t = .af 8 ∧ ls.length = 8
    · obtain ⟨rfl, hl⟩ := hl
      simp only [zeroRows, hl, and_self, if_true] at h
      refine List.Forall₂.cons ⟨by simp [tyOf, nLinkFam], ?_⟩ List.Forall₂.nil
      have hz : ∀ l ∈ ls, l.ev w = 0 := fun l hm => by
        have := h _ (List.mem_map_of_mem hm); simpa [Row.Holds, hone] using this
      simp only [encV, Array.toList_replicate, nLinkFam]
      refine List.ext_getElem (by simp [hl]) fun j h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_replicate]
      exact hz _ (List.getElem_mem _)
    · simp only [zeroRows, hl, if_false] at h
      exact (rej (List.mem_singleton_self _) h).elim
  | [], h => exact (rej (by simp [zeroRows]) h).elim
  | [none], h => exact (rej (by simp [zeroRows]) h).elim
  | _ :: _ :: _, h => exact (rej (by simp [zeroRows]) h).elim

/-- **The segment's `linkWAll` replay is sound** at every index, under `LinkZero`. -/
theorem rtLinkSeg_ok {impl₀ : OpImpl} (base : NodeKind → OpImpl) (hZ : LinkZero impl₀) (ι : Kind) :
    RTOk (implP impl₀ base 1 ι) (Xof 1) rtLinkSeg ι := by
  intro P cs op hc
  cases op
  all_goals first
    | (simp [rtLinkSeg, isLinkW] at hc)
    | skip
  rename_i t p
  refine ⟨fun inp regs q => by simp [evalOp], fun inp w regs vs ok hP _ hrows hev _ => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  have hv : (implP impl₀ base 1 ι).linkWAll ι (rd regs t).toAF (rd regs p).toAF =
      Array.replicate nLinkFam 0 := by
    simp only [implP, one_ne_zero, if_false, OpImpl.fixK, implSeg]; exact hZ _ _
  rw [hv]
  exact zeroRows_sound hP.1 (fun r hr => hrows r (by simp only [rtLinkSeg, isLinkW, if_true]; exact hr))

end N4s
end FR
