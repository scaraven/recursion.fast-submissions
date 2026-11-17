-- New for lvm2 MP-B (cap pruning, stage S2GB; CAP-C4): the plan's walk at S2GB in recursor form, and Q_link's static
-- conditions at S2GB from one kernel evaluation of it (proof help; the S2GS twin is `LvmS2GUPlan.planFacts_of`).
import LvmQCapSound
import LvmS2GUPlan

/-!
# The S2GB plan's facts from one decision

* `openPlanNR`, `heapPlanR`, `planItemRB`, `planItemsRB`, `openItemsRB`: the S2GB walk (`capPrune`) in
  `List.rec`/`Nat.rec` form, each proved equal to its definition by induction (no evaluation).
* `qOkCR`: `qOkCB` over a plan list, its openings and the hashed length (the entries' lanes by `offAtR`, the QLT
  entries' count by `fsCntR`); `qOkCB_eq_R`.
* **`planFacts_ofB`**: over the schedule literal `S` and the parameter literal `q`, one kernel evaluation gives any
  property `X` of the plan list (the caller's stream check), `PlanOkB` with the walk's last entry, and `qOkCB`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- `openPlanN` by `upL` (proof help). -/
noncomputable def openPlanNR (L : Level) (pe : Nat) : List PE :=
  upL (fun j => ⟨.leaf, L.row⟩ :: upL (fun lvl => [⟨.node pe L.height j lvl none, 64⟩]) L.path 0 []) L.t 0 []

theorem openPlanN_eq_R (L : Level) (pe : Nat) : openPlanN L pe = openPlanNR L pe := by
  simp only [openPlanNR, upL_eq, List.append_nil, openPlanN, List.range_eq_range', List.map_eq_flatMap]

/-- `heapPlan` by `upL` (proof help). -/
noncomputable def heapPlanR (L : Level) (pe i0 c ce co : Nat) : List PE :=
  upL (fun n => [⟨.heap pe L.height L.t L.path i0 L.cap (2 ^ L.cap - 1 - n)
    (if 2 ^ L.cap - 1 - n < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩]) (2 ^ L.cap - 2 ^ c) 0 []

theorem heapPlan_eq_R (L : Level) (pe i0 c ce co : Nat) : heapPlan L pe i0 c ce co = heapPlanR L pe i0 c ce co := by
  simp only [heapPlanR, upL_eq, List.append_nil, heapPlan, List.range_eq_range', List.map_eq_flatMap]

/-- `planItem` under `capPrune` with `openPlanNR`, `heapPlanR` (proof help). -/
noncomputable def planItemRB (p : Params) (w : WS) : Item → List PE × WS
  | .read m => ([], { w with pend := w.pend + eBytes * m })
  | .readW m wd => ([], { w with pend := w.pend + wd * m })
  | .cap c r => ([], { w with pcaps := (r, w.pend, nodeBytes * 2 ^ p.capSendBits r.lv c) :: w.pcaps,
                              pend := w.pend + nodeBytes * 2 ^ p.capSendBits r.lv c })
  | .sample => ([⟨.fs w.st, 32 + w.pend⟩], { w.settle with i := w.i + 1, pend := 0, st := w.i })
  | .positions r =>
    let n := (p.level r).nPosQ
    ((List.range n).map (fun k => if k = 0 then ⟨.fs w.st, 32 + w.pend⟩ else ⟨.fs (w.i + k - 1), 32⟩),
      { w.settle with i := w.i + n, pend := 0, st := w.i + n - 1, pe := w.i, posRef := some r,
                      ok := w.ok && decide (1 ≤ n) })
  | .opening r =>
    let L := p.level r
    match w.caps.find? (·.1 == r) with
    | none => ([], { w with ok := false })
    | some (_, ce, co, nb) =>
      let c := p.capSendBits r.lv L.cap
      (appL (openPlanNR L w.pe) (heapPlanR L w.pe w.i c ce co),
        { w with i := w.i + L.t * (1 + L.path) + p.heapQ r.lv L.cap,
                 ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && w.posRef == some r &&
                   decide (1 ≤ L.path) && decide (L.path + L.cap = L.height) && decide (1 ≤ L.cap) &&
                   decide (c ≤ L.cap) && decide (nodeBytes * 2 ^ c = nb) && decide (L.row ≤ queryCap) &&
                   decide (positionsPerAnswer * (L.nPosQ - 1) < L.t) && decide (L.t ≤ positionsPerAnswer * L.nPosQ) })

theorem planItem_eq_RB (p : Params) (hcp : p.capPrune = true) (w : WS) (it : Item) :
    planItem p w it = planItemRB p w it := by
  cases it with
  | opening r =>
    simp only [planItem, planItemRB, hcp, ↓reduceIte]
    generalize List.find? (fun x => x.1 == r) w.caps = o
    rcases o with _ | ⟨_, ce, co, nb⟩
    · rfl
    · simp only [openPlanN_eq_R, heapPlan_eq_R, appL_eq]
  | _ => rfl

/-- `planItems` under `capPrune` by `List.rec` (proof help). -/
noncomputable def planItemsRB (p : Params) (l : List Item) : WS → List PE × WS :=
  l.rec (fun w => ([], w)) (fun it _ ih w =>
    (appL (planItemRB p w it).1 (ih (planItemRB p w it).2).1, (ih (planItemRB p w it).2).2))

theorem planItems_eq_RB (p : Params) (hcp : p.capPrune = true) :
    ∀ (l : List Item) (w : WS), planItems p w l = planItemsRB p l w
  | [], _ => rfl
  | it :: l, w => by
    rw [planItems, planItem_eq_RB p hcp, planItems_eq_RB p hcp l, ← appL_eq]
    rfl

/-- `openItems` under `capPrune` by `List.rec` (proof help). -/
noncomputable def openItemsRB (p : Params) (l : List Item) : WS → List OpenInfo :=
  l.rec (fun _ => []) (fun it _ ih w => appL (openItem p w it) (ih (planItemRB p w it).2))

theorem openItems_eq_RB (p : Params) (hcp : p.capPrune = true) :
    ∀ (l : List Item) (w : WS), openItems p w l = openItemsRB p l w
  | [], _ => rfl
  | it :: l, w => by
    rw [openItems, planItem_eq_RB p hcp, openItems_eq_RB p hcp l, ← appL_eq]
    rfl

/-! ## `qOkCB` over a plan list -/

/-- An entry is an FS query (proof help). -/
def fsBB (e : PE) : Bool := match e.k with | .fs _ => true | _ => false

/-- `n` plus the FS entries of `l`, by `List.rec` (proof help). -/
noncomputable def fsCntRB (l : List PE) : ℕ → ℕ :=
  l.rec (fun n => n) (fun e _ ih n => ih (Nat.add n (cond (fsBB e) 1 0)))

theorem fm_lenB {α : Type} (F : PE × ℕ → Option α) (hF : ∀ e i, (F (e, i)).isSome = fsBB e) :
    ∀ (l : List PE) (i n : ℕ), ((l.zipIdx i).filterMap F).length + n = fsCntRB l n
  | [], _, _ => by simp [fsCntRB]
  | e :: l, i, n => by
    rw [List.zipIdx_cons, List.filterMap_cons]
    show _ = fsCntRB l (Nat.add n (cond (fsBB e) 1 0))
    have h := hF e i
    cases hf : F (e, i) with
    | none =>
      rw [hf, Option.isSome_none] at h
      rw [← h, ← fm_lenB F hF l (i + 1) _]
      rfl
    | some a =>
      rw [hf, Option.isSome_some] at h
      rw [← h, List.length_cons, ← fm_lenB F hF l (i + 1) _]
      show _ = _ + (n + 1)
      omega

theorem fm_len0B {α : Type} (F : PE × ℕ → Option α) (hF : ∀ e i, (F (e, i)).isSome = fsBB e)
    (l : List PE) : ((l.zipIdx 0).filterMap F).length = fsCntRB l 0 :=
  fm_lenB F hF l 0 0

theorem qlt_lenB (p : Params) (lay : Layout) :
    (qltEntries p lay).length = 2 + fsCntRB (plan p) 0 + (17 * nBlk (hashedLen p) - hashedLen p / 8) := by
  rw [qltEntries, List.length_append, List.length_append, List.length_map, List.length_range, fm_len0B _ ?_]
  · rfl
  · intro e i; rcases e with ⟨k, len⟩; cases k <;> rfl

/-- **`qOkCB` over the plan list `L`, its openings `O` and the hashed length `t`** (lanes by `offAtR`). -/
noncomputable def qOkCR (p : Params) (L : List PE) (O : List OpenInfo) (t : ℕ) (lay : Layout) : Bool :=
  decide (2 + fsCntRB L 0 + (17 * nBlk t - t / 8) ≤ 2 ^ lay.aQ) && decide (t / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk t + 4 ≤ 2 ^ lay.m) && decide (t < 2 ^ 64) &&
    (O.all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (o.L.cap = o.L.height - o.L.path) &&
      decide (p.capSendBits o.L.level o.L.cap < o.L.height - o.L.path) &&
      decide (2 ^ (o.L.height - o.L.path - 1) - 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.K) &&
      decide (offAtR L 1 o.i0 / 8 + o.L.t * posStride o.L + 13 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (offAtR L 1 o.ce / 8 + 1 + o.co / 8 + 4 * 2 ^ p.capSendBits o.L.level o.L.cap ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide ((O.map fun o => o.L.t).sum ≤ 2 ^ lay.pa) && p.capPrune &&
    ((List.range p.mainLevels.length).all fun lv => (p.mainLevels.getD lv default).level == lv) &&
    ((List.range p.recLevels.length).all fun lv => (p.recLevels.getD lv default).level == lv)

theorem qOkCB_eq_R (p : Params) (lay : Layout) : qOkCB p lay = qOkCR p (plan p) (opens p) (hashedLen p) lay := by
  have h : ∀ i, eLane p i = offAtR (plan p) 1 i / 8 := fun i => by
    rw [← offAt_eq_R, offAt_eq]; rfl
  simp only [qOkCB, qOkCR, qlt_lenB, heapLane, h]

/-- **The S2GB plan's facts from one decision** (proof help, any parameter set `p` under `capPrune`): over the
schedule literal `S` and the parameter literal `q`, with `|Σ| = t2 + 1`, one kernel evaluation of `h` (the walk
`planItemsRB q S w0`, the openings `openItemsRB q S w0`) gives `X` of the plan (the caller's stream check),
`PlanOkB` with the walk's last entry, and Q_link's `qOkCB` at the layout `ly`. -/
theorem planFacts_ofB {p q : Params} {S : List Item} {n t2 : ℕ} {ly : Layout} (X : List PE → Prop)
    (hS : schedule p = S) (hq : p = q) (hl : hashedLen p = t2 + 1) (hcp : q.capPrune = true)
    (h : let P := planItemsRB q S w0
      let L : List PE := ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP q⟩ :: P.1
      X L ∧ ((P.2.ok = true ∧ P.2.pend = 0 ∧ P.2.pcaps = []) ∧ P.2.i = n) ∧
        qOkCR q L (openItemsRB q S w0) (t2 + 1) ly = true) :
    X (plan p) ∧ (PlanOkB p ∧ (planAll p).2.i = n) ∧ qOkCB p ly = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [plan, planAll, hS, hq, planItems_eq_RB q hcp]; exact h.1
  · rw [PlanOkB, planAll, hS, hq, planItems_eq_RB q hcp]; exact h.2.1
  · rw [qOkCB_eq_R, hl, opens, plan, planAll, hS, hq, planItems_eq_RB q hcp, openItems_eq_RB q hcp]
    exact h.2.2


/-! ## `streamOkLB` from one pass (`passR`'s twin with the heap entries) -/

/-- `entryOkB` with the cap entry's length from `lk` (and the comparisons as `Nat.ble`/`Nat.beq`). -/
def entFB (lk : ℕ → ℕ) (e : PE) (i : ℕ) : Bool :=
  match e.k with
  | .heap pe h t path i0 m k cap =>
    Nat.beq e.len 64 && Nat.ble 2 i0 && Nat.ble 1 t && Nat.ble 1 path && Nat.beq (path + m) h && Nat.ble h 24 &&
      Nat.ble 1 pe && Nat.blt (pe + (t - 1) / 8) i0 && Nat.ble 1 k && Nat.blt k (2 ^ m) &&
      Nat.beq i (i0 + t * (1 + path) + (2 ^ m - 1 - k)) &&
      (match cap with
       | none => true
       | some (ce, co, c) => Nat.beq (co % 8) 0 && Nat.ble 32 co && Nat.ble (2 ^ c) k && Nat.blt k (2 ^ (c + 1)) &&
           Nat.ble (co + 32 * 2 ^ c) (lk ce) && Nat.ble 1 ce && Nat.blt ce i0)
  | _ => entF lk e i

/-- The checks at entry `i` (`elemF`'s twin). -/
def elemFB (lk : ℕ → ℕ) (e : PE) (i : ℕ) : Bool :=
  (Nat.beq i 0 || Nat.beq (e.len % 8) 0) && entFB lk e i && Nat.ble e.len queryCap

/-- **The one pass** from entry `i` (`passR` with `elemFB`). -/
noncomputable def passRB (lk : ℕ → ℕ) (n t1 t2 : ℕ) (P : List PE) : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool :=
  P.rec (fun cur i s1 s2 => cur.isEmpty && Nat.beq i n && Nat.beq s1 t1 && Nat.beq s2 t2)
    (fun e _ ih cur i s1 s2 => elemFB lk e i &&
      cur.casesOn (ih [] (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))
        (fun c rest => bif Nat.beq c.1 i then Nat.beq e.len c.2 && ih rest (i + 1) (s1 + clenC e) (s2 + (40 + e.len))
          else ih (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len))))

section
variable (lk : ℕ → ℕ) (n t1 t2 : ℕ)

theorem passRB_sound : ∀ (P : List PE) (cur : List (ℕ × ℕ)) (i s1 s2 : ℕ),
    passRB lk n t1 t2 P cur i s1 s2 = true →
    (∀ k (hk : k < P.length), elemFB lk P[k] (i + k) = true) ∧
    (∀ x ∈ cur, i ≤ x.1 ∧ (P.getD (x.1 - i) default).len = x.2) ∧
    i + P.length = n ∧ s1 + (P.map clenC).sum = t1 ∧ s2 + (P.map fun e => 40 + e.len).sum = t2
  | [], cur, i, s1, s2, h => by
    change (cur.isEmpty && Nat.beq i n && Nat.beq s1 t1 && Nat.beq s2 t2) = true at h
    simp only [Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    simp
  | e :: es, cur, i, s1, s2, h => by
    change (elemFB lk e i && cur.casesOn (passRB lk n t1 t2 es [] (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))
        (fun c rest => bif Nat.beq c.1 i then Nat.beq e.len c.2 &&
            passRB lk n t1 t2 es rest (i + 1) (s1 + clenC e) (s2 + (40 + e.len))
          else passRB lk n t1 t2 es (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨he, h⟩ := h
    have key : ∃ cur', passRB lk n t1 t2 es cur' (i + 1) (s1 + clenC e) (s2 + (40 + e.len)) = true ∧
        ∀ x ∈ cur, (x.1 = i ∧ e.len = x.2) ∨ x ∈ cur' := by
      rcases cur with _ | ⟨c, rest⟩
      · exact ⟨[], h, fun x hx => absurd hx List.not_mem_nil⟩
      · by_cases hc : c.1 = i
        · have h' : (Nat.beq e.len c.2 && passRB lk n t1 t2 es rest (i + 1) (s1 + clenC e)
              (s2 + (40 + e.len))) = true := by
            simpa [hc, Nat.beq_refl] using h
          rw [Bool.and_eq_true, Nat.beq_eq] at h'
          refine ⟨rest, h'.2, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl ⟨hc, h'.1⟩
          · exact Or.inr hx
        · have hb : Nat.beq c.1 i = false := by
            cases hq : Nat.beq c.1 i
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true hq) hc
          have h' : passRB lk n t1 t2 es (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len)) = true := by
            simpa [hb] using h
          exact ⟨c :: rest, h', fun x hx => Or.inr hx⟩
    obtain ⟨cur', hr, hcur⟩ := key
    obtain ⟨h1, h2, h3, h4, h5⟩ := passRB_sound es cur' (i + 1) _ _ hr
    refine ⟨fun k hk => ?_, fun x hx => ?_, by simp only [List.length_cons]; omega,
      by simp only [List.map_cons, List.sum_cons]; omega, by simp only [List.map_cons, List.sum_cons]; omega⟩
    · cases k with
      | zero => simpa using he
      | succ k =>
        have := h1 k (by simpa using hk)
        rwa [show i + 1 + k = i + (k + 1) by omega] at this
    · rcases hcur x hx with ⟨hxi, hxl⟩ | hx'
      · refine ⟨hxi.ge, ?_⟩
        rw [hxi, Nat.sub_self, List.getD_cons_zero, hxl]
      · obtain ⟨hle, hl⟩ := h2 x hx'
        refine ⟨by omega, ?_⟩
        rw [show x.1 - i = (x.1 - (i + 1)) + 1 by omega, List.getD_cons_succ, hl]

end

/-- `entFB` with a lookup that is the plan's (where it is not `0`) is `entryOkB`. -/
theorem entFB_sound (P : List PE) (lk : ℕ → ℕ) (hlk : ∀ c, lk c = (P.getD c default).len ∨ lk c = 0)
    (e : PE) (i : ℕ) (h : entFB lk e i = true) : entryOkB P e i = true := by
  rcases e with ⟨k, len⟩
  cases k with
  | heap pe hh t path i0 m k cap =>
    rcases cap with _ | ⟨ce, co, c⟩
    · simp only [entFB, entryOkB, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
        decide_eq_true_eq, beq_iff_eq] at h ⊢
      exact h
    · simp only [entFB, entryOkB, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
        decide_eq_true_eq, beq_iff_eq] at h ⊢
      obtain ⟨hA, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ := h
      refine ⟨hA, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, h6⟩, h7⟩⟩
      rcases hlk ce with hl | hl
      · rwa [← hl]
      · rw [hl] at h5
        exfalso
        have : 1 ≤ 2 ^ c := Nat.one_le_two_pow
        omega
  | q0 => exact entF_sound P lk hlk ⟨.q0, len⟩ i h
  | fs st => exact entF_sound P lk hlk ⟨.fs st, len⟩ i h
  | leaf => exact entF_sound P lk hlk ⟨.leaf, len⟩ i h
  | node pe hh j lvl cap => exact entF_sound P lk hlk ⟨.node pe hh j lvl cap, len⟩ i h

/-- **What the one pass gives** for any plan `P` and cap table `tbl` (`sound_of`'s twin). -/
theorem sound_ofB {P : List PE} {tbl : List (ℕ × ℕ)} {n c sl : ℕ} (h : passRB (capLk tbl) n c sl P tbl 0 0 0 = true) :
    (∀ k (hk : k < P.length), elemFB (capLk tbl) P[k] k = true) ∧
    (∀ x ∈ tbl, (P.getD x.1 default).len = x.2) ∧
    P.length = n ∧ (P.map clenC).sum = c ∧ (P.map fun e => 40 + e.len).sum = sl := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := passRB_sound _ _ _ _ _ _ _ _ _ h
  refine ⟨fun k hk => ?_, fun x hx => ?_, by rw [Nat.zero_add] at h3; exact h3,
    by rw [Nat.zero_add] at h4; exact h4, by rw [Nat.zero_add] at h5; exact h5⟩
  · have := h1 k hk
    rwa [Nat.zero_add] at this
  · have := (h2 x hx).2
    rwa [Nat.sub_zero] at this

/-- **`streamOkLB` from the one pass** (`streamOkL_of`'s twin). -/
theorem streamOkLB_of {P : List PE} {tbl : List (ℕ × ℕ)} {n c sl : ℕ}
    (h : passRB (capLk tbl) n c sl P tbl 0 0 0 = true) : streamOkLB P = true := by
  have hlk := capLk_spec P tbl (sound_ofB h).2.1
  simp only [streamOkLB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have hk' : k + 1 < P.length := by rw [List.length_tail] at hk; omega
    have h := (sound_ofB h).1 _ hk'
    simp only [elemFB, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    simp only [List.getElem_tail, beq_iff_eq]
    omega
  · obtain ⟨hk, he⟩ : ∃ hk : x.2 < P.length, P[x.2] = x.1 := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      rw [List.getElem?_eq_some_iff] at this
      exact this
    have h := (sound_ofB h).1 _ hk
    simp only [elemFB, Bool.and_eq_true] at h
    rw [← he]
    exact entFB_sound _ _ hlk _ _ h.1.2

/-- **`StreamOkB` from the one pass**, with `hashedLen p = t2 + 1` (`streamOk_ofR`'s twin). -/
theorem streamOkB_ofR {p : Params} {tbl : List (ℕ × ℕ)} {n t1 t2 : ℕ}
    (h : passRB (capLk tbl) n t1 t2 (plan p) tbl 0 0 0 = true) (hh : hashedLen p = t2 + 1) : StreamOkB p := by
  refine ⟨streamOkLB_of h, ?_⟩
  have hs : slenS (lens p) = t2 := by
    rw [slenS, lens, List.map_map]
    exact (sound_ofB h).2.2.2.2
  rw [hh, hs, Nat.add_comm]

end Lvm.E2Q
