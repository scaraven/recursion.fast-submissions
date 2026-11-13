-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's mini-bus phase: `miniG` replays V_S's `dMiniT` (roll 7's
-- `busG_replays` at the mini-bus's depth, `tabG_replays` on its tables, and the fixed address columns checked in the
-- circuit by `powColG`, V_S's `tableCheckR`).
import LvmQTypedHarB
import LvmQAsmHarTails

/-!
# The mini-bus in the circuit

* **`miniG_replays`**: on tables `tabs` that are all sumcheck tables, whose shapes, rounds and depth are the
  circuit's (`TData.mbS`, `mbR`, `mbD`), and whose every fixed column `x ↦ g^{b + s x}` is listed in `TData.mbFix`,
  `miniG` replays `dMiniT p (M3.real p fun _ ↦ tabs) tabs pub` from `P` to the table phase's end; the evaluations
  are its table cells' values.
* **`mbT_sumcheck`, `mbT_fix`**: B1-Q's mini-bus tables (`mbT`: the seed arrays, then the read tables) meet the
  first and the last condition at any placements (`mbFixOf`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.QAsm Lvm.Q1 Lvm.M3 DM

/-- Every fixed column of `tabs` is listed in `fx` with its power closed form `g^b·powEval r (g^s)`. -/
def FixListed (tabs : List Tab) (fx : List (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ k (t : Tab), tabs[k]? = some t → ∀ i (f : Nat → FK) (e : List FE → FE), t.cols[i]? = some (.fix f e) →
    ∃ b s, (k, i, b, s) ∈ fx ∧ ∀ r, e r = FE.ofK (FK.x ^ b) * powEval r (FK.x ^ s)

/-- **B1-Q's mini-bus tables are all sumcheck tables** (a seed array has a seed, a read table a read). -/
theorem mbT_sumcheck (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    sumcheckTabs (mbT C wordK fin cnt) = mbT C wordK fin cnt := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
    simp [InArr.tab]
  · simp only [capReads, List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    simp [readTab]

/-- Seed array `k` of `mbArrs` (`fin` only changes its finalize column). -/
theorem mbArrs_get (C : QCfg) (fin : Nat → Bool × Nat) (k : Nat) :
    (mbArrs C fin)[k]? = ((mbBlocks C.p)[k]?).map fun q =>
      ⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], fin k, none⟩ := by
  rw [mbArrs, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add]
  rfl

/-- **B1-Q's mini-bus tables' fixed columns are `mbFixOf`'s** (a seed array's address column; a read table has
none). -/
theorem mbT_fix (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    FixListed (mbT C wordK fin cnt) (mbFixOf C) := by
  intro k t hk i f e hc
  rw [mbT, List.getElem?_append] at hk
  split at hk
  · rw [List.getElem?_map, mbArrs_get] at hk
    cases hb : (mbBlocks C.p)[k]? with
    | none => simp [hb] at hk
    | some q =>
      simp only [hb, Option.map_some, Option.some.injEq] at hk
      subst hk
      simp only [InArr.tab, InArr.vcols, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append] at hc
      match i, hc with
      | 2, hc =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          ColSrc.fix.injEq] at hc
        obtain ⟨-, rfl⟩ := hc
        refine ⟨(lay C).sb + 17 * q.2 + q.1, 17, ?_, fun r => rfl⟩
        rw [mbFixOf, List.mem_map]
        refine ⟨(⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], (false, 0),
          none⟩, k), ?_, rfl⟩
        rw [List.mem_zipIdx_iff_getElem?, mbArrs_get, hb]
        rfl
      | 0, hc => simp at hc
      | 1, hc => simp at hc
      | _ + 3, hc => simp at hc
  · simp only [capReads, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨x, -, rfl⟩ := hk
    simp only [readTab] at hc
    match i, hc with
    | 0, hc => simp at hc
    | 1, hc => simp at hc
    | 2, hc => simp at hc
    | _ + 3, hc => simp at hc

/-- The GKR layers end on a lane boundary (as in `busG_sound`). -/
theorem layersEnd_mod8 : ∀ (sts : List Nat) (n Q : Nat), Q % 8 = 0 → layersEnd sts n Q % 8 = 0
  | [], _, _, hQ => hQ
  | st :: sts, n, Q, hQ => layersEnd_mod8 sts _ _ (stepEnd_mod st n Q hQ)

/-- **The circuit's fixed-column checks give `tableCheckR`**: where `miniG`'s `powColG`/`assertEq` checks over `fx`
hold (gate on), every fixed column listed in `fx` evaluates at its table's point cells to its value cell. -/
theorem fixCheck_of {tabs : List Tab} {fx : List (Nat × Nat × Nat × Nat)} (hfix : FixListed tabs fx)
    {c : Ctx} {M : Mem} {z g : Cell} (hz : z.val M = 0) (hg : g.val M = 1)
    (tab : List (List Cell × List Cell)) {q : Ptr}
    (hok : Lvm.QSig.Ok c M (seqAll (fx.map fun f => do
      let e := tab.getD f.1 default
      let v ← powColG z f.2.2.1 f.2.2.2 e.1
      assertEq (e.2.getD f.2.1 z) v g)) q) :
    tableCheckR tabs (tab.map fun e => (vs M e.1, vs M e.2)) = true := by
  unfold tableCheckR
  rw [List.all_eq_true]
  rintro ⟨t, pt, ev⟩ hmem
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hk1, hk2⟩ := List.getElem?_zip_eq_some.mp hk
  rw [List.getElem?_map, Option.map_eq_some_iff] at hk2
  obtain ⟨x, hx, hxe⟩ := hk2
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  rw [List.all_eq_true]
  rintro ⟨col, i⟩ hci
  rw [List.mem_zipIdx_iff_getElem?] at hci
  cases col with
  | com _ _ => rfl
  | fix f e =>
    obtain ⟨b, s, hmemfx, he⟩ := hfix k t hk1 i f e hci
    obtain ⟨q', hq'⟩ := Lvm.QSig.ok_seqAll _ q hok _ (List.mem_map_of_mem hmemfx)
    have htk : tab.getD k default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    obtain ⟨h1, h2, -⟩ := Lvm.QSig.ok_bind' hq'
    simp only [htk] at h1 h2
    have hv := powColG_spec hz b s x.1 q' h1.1
    have heq := Lvm.QAcc.assertEqE_spec h2 hg
    simp only [beq_iff_eq]
    rw [he]
    simp only [vs]
    rw [← hv, ← heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x.2[i]? with
    | none => exact hz.symm
    | some y => rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The mini-bus replayed** (soundness direction): wherever `miniG`'s rows hold and assert (gate on), `dMiniT` on
`tabs` from any state at `P` with `ok` keeps `ok`, ends at the table phase's end, and its evaluations are the table
cells' values. -/
theorem miniG_replays (hS : Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (p : Params)
    (hl : p.leafdecReads = 1) (Td : TData) (tabs : List Tab) (hsc : sumcheckTabs tabs = tabs)
    (hS' : Td.mbS = tabs.map Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed tabs Td.mbFix) (pub : Pub) {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd Td.mbS Td.mbR (busEndD Td.mbD P) + 40 ≤ 8 * T) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig (TypedV.dMiniT p (M3.real p fun _ => tabs) tabs pub) (miniG z o g Td P) ptr P
      (tabEnd Td.mbS Td.mbR (busEndD Td.mbD P)) fun v t => v = t.2.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hout : (miniG z o g Td P ptr).1 = ((busGD Td.mbD z o g P ptr).1,
      (tabG Td.mbS Td.mbR (busEndD Td.mbD P) z o g (busGD Td.mbD z o g P ptr).1
        (ptr.adv (busGD Td.mbD z o g P ptr).2)).1) := rfl
  obtain ⟨hB, hok1, -⟩ := Lvm.QSig.ok_bind' hok
  obtain ⟨hTb, hok2, -⟩ := Lvm.QSig.ok_bind' hok1
  obtain ⟨hFx, -⟩ := Lvm.QSig.ok_bind' hok2
  rw [hout]
  clear hout hok hok1 hok2
  have hS0 : Td.mbS = (sumcheckTabs tabs).map Tab.shape := by rw [hsc]; exact hS'
  rw [hS0, hR, hD] at hTb hFx hT ⊢
  rw [hD] at hB
  have e1 : busGD p.busDepth z o g P = busG p z o g P := rfl
  have e2 : busEndD p.busDepth P = busEnd p P := rfl
  rw [e1] at hB hTb hFx ⊢
  rw [e2] at hTb hFx hT ⊢
  have hT1 : busEnd p P + 40 ≤ 8 * T := by unfold tabEnd at hT; omega
  have hP2 : busEnd p P % 8 = 0 := by
    have := layersEnd_mod8 (gkrSteps p.busDepth) 0 (busP1 P + 48) (by simp only [busP1, busBits]; omega)
    simp only [busEnd]; omega
  obtain ⟨b1, b2, b3⟩ := busG_replays (c := c) hS hz ho hg p hl hP hT1 ptr hB s hs hsok
  obtain ⟨hal, d, hpt⟩ := busG_fst p z o g P ptr
  generalize (busG p z o g P ptr).1 = bus at b3 hal hpt hTb hFx ⊢
  obtain ⟨hbv, h3⟩ := busR_eq b3
  rw [dMiniT_eq, bind_run']
  generalize busPh p sig s = BB at b1 b2 hbv ⊢
  obtain ⟨bv, s1⟩ := BB
  simp only at b1 b2 hbv
  subst hbv
  simp only [busV, bind_run', require_run']
  have hok2 : ((M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩).ok = true := by
    show ((vs M bus.vals).length == 3 && [(0 : FE)] == [0]) = true
    rw [h3]; decide
  set bo := (M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩
  have rt := tabG_replays (c := c) hS hz ho hg hzE hoE p (M3.real p fun _ => tabs) pub tabs rfl bus
    (countRoot := bus.cnt.val M) (leafdec := [0]) rfl rfl rfl rfl
    (by rw [hal]; simp [vs, busBits])
    (by rw [hal]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    (by rw [hpt]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    bo rfl hP2 hT (ptr.adv (busG p z o g P ptr).2)
  obtain ⟨t1, t2, t3⟩ := rt hTb ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ b2 (by rw [hok2, b1]; rfl)
  generalize tabPh p (M3.real p fun _ => tabs) pub bo (vs M bus.pt) sig ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ = TT
    at t1 t2 t3 ⊢
  obtain ⟨ev, s3⟩ := TT
  simp only [TabR] at t1 t2 t3
  subst t3
  generalize (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds (busEnd p P) z o g bus
    (ptr.adv (busG p z o g P ptr).2)).1 = tab at hFx ⊢
  rw [pure_run']
  refine ⟨?_, t2, rfl⟩
  rw [hsc, fixCheck_of hfix hz hg tab hFx, t1]
  rfl

end

end Lvm.Har
