-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's base: the soundness of the guard check `harChkB`'s region half
-- (`TdOk`: the circuit's `TData` names V_S's regions), the mini-bus phase `dMiniT` split as roll 7's phases 2–3
-- (`busPh`, `require bus.ok`, `tabPh`, then the fixed columns' check), and the reader's positions of the typed
-- phases.
import LvmQTypedHarChk
import LvmQAsmHarTop

/-!
# The typed HAR's base

* **`TdOk T N`** (from `tdMatchB T N = true`, `tdOk_of`): per source, V_S's regions are the circuit's (base, size,
  target, in order); one `S_flat` region (`2^19` words from position 0), one `PUB` region (`2^10` lanes from lane 0),
  one word `1`.
* **`dMiniT_eq`**: `dMiniT` is roll 7's bus phase `busPh`, the bus check, the table phase `tabPh` and the fixed
  columns' check `tableCheckR`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)

/-! ## The regions -/

/-- **The circuit's regions are V_S's** (`tdMatchB`'s meaning). -/
structure TdOk (T : TData) (N : TNat) : Prop where
  com : (N.regsOf .com).map nTrip = T.com.map tTrip
  ks : (N.regsOf .ks).map nTrip = T.ks.map tTrip
  sig : (N.regsOf .sigma).map nTrip = T.sig.map tTrip
  sflat : N.regsOf .sflat = [⟨T.sflat, 19, .sflat, 0⟩]
  pub : N.regsOf .pub = [⟨T.pub, 10, .pub, 0⟩]
  one : (N.regsOf .one).map (fun g => (g.base, g.log)) = [(T.one, 0)]
  qlt : T.qlt = none

theorem regsOf_src {N : TNat} {s : Lvm.Typed.YSrc} {g : NReg} (h : g ∈ N.regsOf s) : g.src = s := by
  simp only [TNat.regsOf, List.mem_filter, beq_iff_eq] at h
  exact h.2

theorem regsOf_one_trip {N : TNat} {s : Lvm.Typed.YSrc} {b l d : Nat} (h : (N.regsOf s).map nTrip = [(b, l, d)]) :
    N.regsOf s = [⟨b, l, s, d⟩] := by
  match hN : N.regsOf s, h with
  | [g], h' =>
    have hs : g.src = s := regsOf_src (g := g) (by rw [hN]; exact List.mem_singleton_self g)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, nTrip, Prod.mk.injEq, and_true] at h'
    obtain ⟨g1, g2, g3, g4⟩ := g
    simp only at hs h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    rw [hs]

/-- **`tdMatchB`'s soundness.** -/
theorem tdOk_of {T : TData} {N : TNat} (h : tdMatchB T N = true) : TdOk T N := by
  simp only [tdMatchB, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, regsOf_one_trip h4, regsOf_one_trip h5, h6, h7⟩

/-! ## The mini-bus phase -/

/-- **`dMiniT` as roll 7's phases 2–3** (`busPh`, the bus check, `tabPh`), then the fixed columns' check. -/
theorem dMiniT_eq (p : Params) (m : M3) (tabs : List Lvm.M3.Tab) (pub : Pub) :
    TypedV.dMiniT p m tabs pub = (do
      let (alphas, beta, countRoot, point, values, leafdec) ← busPh p
      let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
      require bus.ok
      let evals ← tabPh p m pub bus point
      require (Lvm.M3.tableCheckR (Lvm.M3.sumcheckTabs tabs) evals)
      pure evals) := by
  funext sig s
  simp only [TypedV.dMiniT, busPh, tabPh, bind_assoc, pure_bind]

end Lvm.Har
