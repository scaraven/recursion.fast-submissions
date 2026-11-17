-- New for lvm (WP-11b-QL): Q_link's soundness, from its gadgets' specifications.
import LvmQLinkBridge
import LvmQBuildLemmas

-- (GOLF2: 11 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

-- ===== merged from `LvmQLinkPlan` (GOLF module merge: `LvmQLinkPlan.lean` is now a stub importing `LvmQLinkSound`) =====
section
-- New for lvm (WP-11b-QL): the openings of the plan, and the lanes of their entries.

/-!
# The openings of the plan

`opens p` lists the schedule's openings (`OpenInfo`: first entry, level, positions entry, cap
entry and offset), by the same walk as the plan. `open_of_entry`: every leaf or node entry of the
plan lies in an opening, as the corresponding entry of its `openPlan`; `openPlan_getD` reads that
entry; `eLane_open`: inside an opening the lanes are affine in the position and the level.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay

/-- An opening of the plan. -/
structure OpenInfo where
  /-- Its first entry. -/
  i0 : Nat
  /-- Its level. -/
  L : Level
  /-- The first positions entry. -/
  pe : Nat
  /-- The cap's entry. -/
  ce : Nat
  /-- The cap's byte offset in that entry's query. -/
  co : Nat
  deriving Repr, Inhabited

/-- The opening an item makes (the walk's `planItem`). -/
def openItem (p : Params) (w : WS) : Item → List OpenInfo
  | .opening r =>
    match w.caps.find? (·.1 == r) with
    | none => []
    | some (_, ce, co, _) => [⟨w.i, p.level r, w.pe, ce, co⟩]
  | _ => []

/-- The openings of a list of items. -/
def openItems (p : Params) : WS → List Item → List OpenInfo
  | _, [] => []
  | w, it :: its => openItem p w it ++ openItems p (planItem p w it).2 its

/-- **The openings of the plan.** -/
def opens (p : Params) : List OpenInfo := openItems p w0 (schedule p)

/-- An entry is a leaf or a node. -/
def _root_.Lvm.Replay.EK.isOpen : EK → Bool
  | .leaf => true
  | .node .. => true
  | _ => false

theorem planItem_open (p : Params) (w : WS) (it : Item) {x : Nat} (hx : x < (planItem p w it).1.length)
    (he : ((planItem p w it).1.getD x default).k.isOpen = true) :
    ∃ o ∈ openItem p w it, o.i0 = w.i ∧ (planItem p w it).1 = openPlan o.L o.pe o.ce o.co := by
  cases it with
  | read m => simp [planItem] at hx
  | readW m wd => simp [planItem] at hx
  | cap c r => simp [planItem] at hx
  | sample =>
    simp only [planItem, List.length_singleton, Nat.lt_one_iff] at hx
    subst hx; simp [planItem, EK.isOpen] at he
  | positions r =>
    simp only [planItem, List.length_map, List.length_range] at hx
    simp only [planItem, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some] at he
    split_ifs at he <;> simp [EK.isOpen] at he
  | opening r =>
    rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
    · simp [planItem, hf] at hx
    · refine ⟨⟨w.i, p.level r, w.pe, ce, co⟩, by simp [openItem, hf], rfl, by simp [planItem, hf]⟩

theorem openItems_open (p : Params) : ∀ (its : List Item) (w : WS) {x : Nat},
    x < (planItems p w its).1.length → ((planItems p w its).1.getD x default).k.isOpen = true →
    ∃ o ∈ openItems p w its, o.i0 ≤ w.i + x ∧ w.i + x < o.i0 + (openPlan o.L o.pe o.ce o.co).length ∧
      (planItems p w its).1.getD x default = (openPlan o.L o.pe o.ce o.co).getD (w.i + x - o.i0) default
  | [], _, _, hx, _ => by simp [planItems] at hx
  | it :: its, w, x, hx, he => by
    simp only [planItems, List.length_append] at hx he ⊢
    by_cases h1 : x < (planItem p w it).1.length
    · rw [List.getD_append _ _ _ _ h1] at he ⊢
      obtain ⟨o, ho, hi, hp⟩ := planItem_open p w it h1 he
      refine ⟨o, by simp [openItems, ho], by (clear * - hi; omega), by rw [← hp, hi]; (clear * - h1; omega), ?_⟩
      rw [hi, show w.i + x - w.i = x by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - w x; omega)), hp]
    · rw [List.getD_append_right _ _ _ _ (by (clear * - h1; omega))] at he ⊢
      obtain ⟨o, ho, h2, h3, h4⟩ := openItems_open p its (planItem p w it).2 (x := x - (planItem p w it).1.length)
        (by (clear * - hx h1; omega)) he
      rw [planItem_i] at h2 h3 h4
      refine ⟨o, by simp [openItems, ho], by (clear * - h1 h2; omega), by (clear * - h1 h3; omega), ?_⟩
      rw [h4]; congr 1; (clear * - h1 h2; omega)

/-- **Every leaf or node entry lies in an opening.** -/
theorem open_of_entry (p : Params) {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpen = true) :
    ∃ o ∈ opens p, o.i0 ≤ i ∧ i < o.i0 + (openPlan o.L o.pe o.ce o.co).length ∧
      (plan p).getD i default = (openPlan o.L o.pe o.ce o.co).getD (i - o.i0) default := by
  have h2 : 2 ≤ i := by
    rcases i with _ | _ | i
    · rw [plan_zero] at he; simp [EK.isOpen] at he
    · rw [plan_one] at he; simp [EK.isOpen] at he
    · (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - i; omega))
  have hpl : (plan p).getD i default = (planAll p).1.getD (i - 2) default := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by (clear * - h2; omega)⟩
    simp [plan, List.getD_eq_getElem?_getD]
  rw [hpl] at he ⊢
  have := openItems_open p (schedule p) w0 (x := i - 2) (by rw [plan_length] at hi; simp [planAll] at hi ⊢; (clear * - hi h2; omega)) he
  simp only [w0] at this
  rw [show 2 + (i - 2) = i by (clear * - h2 this; omega)] at this
  exact this

/-! ## Inside an opening -/

theorem openPlan_length (L : Level) (pe ce co : Nat) :
    (openPlan L pe ce co).length = L.t * (1 + L.path) := by
  simp [openPlan, List.length_flatMap]; left; ring

/-- The entry at position `j`, slot `y` (`0` the leaf, `1 + lvl` the nodes) of an opening. -/
theorem openPlan_getD (L : Level) (pe ce co : Nat) {j y : Nat} (hj : j < L.t) (hy : y < 1 + L.path) :
    (openPlan L pe ce co).getD (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩
      else ⟨.node pe L.height j (y - 1) (if y = L.path then some (ce, co, L.path) else none), 64⟩ := by
  suffices h : ∀ (n k : Nat) (j : Nat), j < n →
      ((List.range' k n).flatMap fun j => (⟨.leaf, L.row⟩ : PE) :: (List.range L.path).map fun lvl =>
        ⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩).getD
          (j * (1 + L.path) + y) default =
      if y = 0 then ⟨.leaf, L.row⟩
      else ⟨.node pe L.height (k + j) (y - 1) (if y = L.path then some (ce, co, L.path) else none), 64⟩ by
    simpa [openPlan, List.range_eq_range'] using h L.t 0 j hj
  intro n
  induction n with
  | zero => intro k j hj; (clear * - hj; omega)
  | succ n ih =>
    intro k j hj
    rw [List.range'_succ, List.flatMap_cons]
    rcases j with _ | j
    · simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      rw [List.getD_append _ _ _ _ (by simp; (clear * - hy; omega))]
      rcases y with _ | y
      · simp
      · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by (clear * - hy; omega))]
        simp [Nat.add_one_inj]
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have := ih (k + 1) j (by (clear * - hj; omega))
      rw [show k + (j + 1) = k + 1 + j by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      rw [← this]
      congr 1
      simp only [Nat.succ_mul, List.length_cons, List.length_map, List.length_range]
      ring_nf; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j L y; omega))

theorem openItems_al (p : Params) {P : List PE} : ∀ (its : List Item) (w : WS),
    Al P w.i (planItems p w its).1 → ∀ o ∈ openItems p w its, Al P o.i0 (openPlan o.L o.pe o.ce o.co)
  | [], _, _, o, ho => by simp [openItems] at ho
  | it :: its, w, hal, o, ho => by
    obtain ⟨h1, h2⟩ := Al_planItems p hal
    simp only [openItems, List.mem_append] at ho
    rcases ho with ho | ho
    · cases it with
      | opening r =>
        rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
        · simp [openItem, hf] at ho
        · simp only [openItem, hf, List.mem_singleton] at ho
          subst ho
          simpa [planItem, hf] using h1
      | _ => simp [openItem] at ho
    · exact openItems_al p its _ h2 o ho

/-- Every opening sits in the plan at its first entry. -/
theorem opens_al (p : Params) {o : OpenInfo} (ho : o ∈ opens p) : Al (plan p) o.i0 (openPlan o.L o.pe o.ce o.co) := by
  refine openItems_al p (schedule p) w0 ⟨by simp [w0, plan_length, planAll], fun x hx => ?_⟩ o ho
  show (plan p).getD (2 + x) default = _
  simp only [plan, planAll, List.getD_eq_getElem?_getD]
  rw [show 2 + x = x + 1 + 1 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
  simp

theorem opens_i0 (p : Params) {o : OpenInfo} (ho : o ∈ opens p) : 2 ≤ o.i0 := by
  suffices h : ∀ (its : List Item) (w : WS), 2 ≤ w.i → ∀ o ∈ openItems p w its, 2 ≤ o.i0 from
    h _ _ (by simp [w0]) o ho
  intro its
  induction its with
  | nil => intro w _ o ho; simp [openItems] at ho
  | cons it its ih =>
    intro w hw o ho
    simp only [openItems, List.mem_append] at ho
    rcases ho with ho | ho
    · cases it with
      | opening r =>
        rcases hf : w.caps.find? (·.1 == r) with _ | ⟨r', ce, co, nb⟩
        · simp [openItem, hf] at ho
        · simp only [openItem, hf, List.mem_singleton] at ho; subst ho; exact hw
      | _ => simp [openItem] at ho
    · exact ih _ (by rw [planItem_i]; (clear * - hw; omega)) o ho

/-- The lane offset of slot `y` (`0` the leaf, `1 + lvl` the nodes) from its position's leaf. -/
def slotOff (L : Level) (y : Nat) : Nat := if y = 0 then 0 else 5 + L.row / 8 + 13 * (y - 1)

/-- The lanes of one position of an opening. -/
def posStride (L : Level) : Nat := 5 + L.row / 8 + 13 * L.path

/-- **The lanes inside an opening are affine.** -/
theorem eLane_open {p : Params} (hS : StreamOk p) {o : OpenInfo} (ho : o ∈ opens p) {j y : Nat}
    (hj : j < o.L.t) (hy : y ≤ o.L.path) :
    eLane p (o.i0 + j * (1 + o.L.path) + y) = eLane p o.i0 + j * posStride o.L + slotOff o.L y := by
  have hal := opens_al p ho
  have h2 := opens_i0 p ho
  have hlen := hal.1
  rw [openPlan_length] at hlen
  have entry : ∀ j' < o.L.t, ∀ y' < 1 + o.L.path, ((plan p).getD (o.i0 + j' * (1 + o.L.path) + y') default).len =
      if y' = 0 then o.L.row else 64 := by
    intro j' hj' y' hy'
    rw [Nat.add_assoc, hal.2 _ (by rw [openPlan_length]; nlinarith), openPlan_getD _ _ _ _ hj' hy']
    split <;> rfl
  have hrow8 : o.L.row % 8 = 0 := by
    have := streamOk_len hS.1 (i := o.i0) (by (clear * - h2; omega)) (by nlinarith)
    have e := entry 0 (by (clear * - hj; omega)) 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - o; omega)))
    simp only [Nat.zero_mul, Nat.add_zero, ite_true] at e
    rw [e] at this; exact this
  -- within a position
  have within : ∀ j' < o.L.t, ∀ y' ≤ o.L.path, eLane p (o.i0 + j' * (1 + o.L.path) + y') =
      eLane p (o.i0 + j' * (1 + o.L.path)) + slotOff o.L y' := by
    intro j' hj' y'
    induction y' with
    | zero => intro _; simp [slotOff]
    | succ y' ih =>
      intro hy'
      rw [← Nat.add_assoc, eLane_succ hS.1 (by (clear * - h2; omega)) (by nlinarith), ih (by (clear * - hy'; omega)), entry j' hj' y' (by (clear * - hy'; omega))]
      simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      split
      · next h => subst h; simp; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
      · next h => (clear * - h; omega)
  have leaf : ∀ j' < o.L.t, eLane p (o.i0 + j' * (1 + o.L.path)) = eLane p o.i0 + j' * posStride o.L := by
    intro j'
    induction j' with
    | zero => intro _; simp
    | succ j' ih =>
      intro hj'
      have hstep : o.i0 + (j' + 1) * (1 + o.L.path) = o.i0 + j' * (1 + o.L.path) + o.L.path + 1 := by ring
      rw [hstep, eLane_succ hS.1 (by (clear * - h2 hstep; omega)) (by nlinarith), within j' (by (clear * - hj'; omega)) o.L.path le_rfl,
        ih (by (clear * - hj'; omega)), entry j' (by (clear * - hj'; omega)) o.L.path (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - o; omega)))]
      simp only [slotOff, posStride]
      split
      · next h => rw [h]; ring_nf
      · next h =>
        have : 13 * o.L.path = 13 * (o.L.path - 1) + 13 := by (clear * - hstep h; omega)
        rw [Nat.add_mul, this]; ring_nf
  rw [within j hj y hy, leaf j hj]

end Lvm.QLink
end
-- ===== end of `LvmQLinkPlan` =====

-- ===== merged from `LvmQLinkGadgets` (GOLF module merge: `LvmQLinkGadgets.lean` is now a stub importing `LvmQLinkSound`) =====
section
-- New for lvm (WP-11b-QL): Q_link's LoopIR gadgets, written with LvmQBuild.

/-!
# Q_link's gadgets

* **`checkLoop dims gate chks`**: one loop block; per iteration and per check `⟨A, B, k, k'⟩` (affine
  `K` operands) a `lin` row `A + k·B + k'` and an `assert0` of it under `gate`. `checkLoop_spec`: when
  the gate is `1`, `A = k·B + k'` at every iteration (characteristic 2). Length lanes (`A = len`:
  `k = 0`, `k' = len`), FS state copies (`A = B`: `k = 1`) and constant lanes are checks.
* **`nodeLoop`**: per iteration a node query's selection: per lane `S = L + R`, `c = β·S + L`,
  `c = P`. `nodeLoop_spec`: with `β` a bit, `P = (β = 1 ? R : L)` on each of the four lanes.
* **`capLoop`**: per iteration the cap check of a path: the address `g^(lo + 4 · Σ_z β_z 2^z)` from
  the cap bits, its three successors, four `readd` and four equality checks. `capLoop_spec`: with
  bits and `GInj`, the four answer lanes are the cap node's.
* **`split`**: a family of `n` iterations as loops of `2^a` iterations at the binary digits of `n`
  (`chunks`); `split_cover`: every `k < n` lies in one chunk.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## Chunks -/

/-- The binary chunks of `[s, s + rem)`: `(start, log size)`, largest first (greedy, at most
`fuel` of them). -/
def chunksG : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel + 1, s, rem => if rem = 0 then [] else
      (s, rem.log2) :: chunksG fuel (s + 2 ^ rem.log2) (rem - 2 ^ rem.log2)

/-- The chunks of `[0, n)`: one per binary digit of `n`. -/
def chunks (n : Nat) : List (Nat × Nat) := chunksG n 0 n

theorem chunksG_cover : ∀ (fuel s rem k : Nat), rem ≤ fuel → s ≤ k → k < s + rem →
    ∃ c ∈ chunksG fuel s rem, c.1 ≤ k ∧ k < c.1 + 2 ^ c.2
  | 0, _, _, _, h, h1, h2 => by omega
  | fuel + 1, s, rem, k, h, h1, h2 => by
    have hr : rem ≠ 0 := by (clear * - h1 h2; omega)
    have hle := Nat.log2_self_le hr
    simp only [chunksG, hr, ite_false]
    by_cases hk : k < s + 2 ^ rem.log2
    · exact ⟨(s, rem.log2), by simp, h1, hk⟩
    · have hpos := Nat.two_pow_pos rem.log2
      obtain ⟨c, hc, hc1, hc2⟩ := chunksG_cover fuel (s + 2 ^ rem.log2) (rem - 2 ^ rem.log2) k (by (clear * - h hle hpos; omega))
        (by (clear * - hk; omega)) (by (clear * - h2 hle; omega))
      exact ⟨c, by simp [hc], hc1, hc2⟩

/-- **Every `k < n` lies in a chunk.** -/
theorem chunks_cover {n k : Nat} (hk : k < n) : ∃ c ∈ chunks n, c.1 ≤ k ∧ k < c.1 + 2 ^ c.2 :=
  chunksG_cover n 0 n k le_rfl (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - k; omega))) (by (clear * - k n hk; omega))

/-! ## Check loops -/

/-! ## The table-driven lane checks (QLT) -/

/-- The template of the QLT loop: per iteration `k`, from the table cells `qt + 3k + {0, 1, 2}`
(`α = g^e₁`, `β = g^e₂`, `v`): the addresses `g^l·α` (`l = 1…4`) and `g^l·β` (`l = 1…3`), nine
`readd`s (region `[lo, lo + 2^m)`), and the checks `mem[e₁] = v`, `mem[e₁ + 1 + l] = mem[e₂ + l]`. -/
def qltTpl (qt lo m : Nat) (gate : Cell) : List LRow :=
  let α : Opd := .abs ⟨.K, qt, [3]⟩
  let β : Opd := .abs ⟨.K, qt + 1, [3]⟩
  let v : Opd := .abs ⟨.K, qt + 2, [3]⟩
  [⟨.lin (gpow 1 + 1) 0, .K, [α, α]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [α, α]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [α, α]⟩, ⟨.lin (gpow 4 + 1) 0, .K, [α, α]⟩,
   ⟨.lin (gpow 1 + 1) 0, .K, [β, β]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [β, β]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [β, β]⟩,
   ⟨.readd lo m, .K, [α]⟩, ⟨.readd lo m, .K, [.cur 0]⟩, ⟨.readd lo m, .K, [.cur 1]⟩,
   ⟨.readd lo m, .K, [.cur 2]⟩, ⟨.readd lo m, .K, [.cur 3]⟩,
   ⟨.readd lo m, .K, [β]⟩, ⟨.readd lo m, .K, [.cur 4]⟩, ⟨.readd lo m, .K, [.cur 5]⟩,
   ⟨.readd lo m, .K, [.cur 6]⟩,
   ⟨.lin 1 0, .K, [.cur 7, v]⟩, ⟨.assert0, .K, [.cur 16, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 8, .cur 12]⟩, ⟨.assert0, .K, [.cur 18, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 9, .cur 13]⟩, ⟨.assert0, .K, [.cur 20, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 10, .cur 14]⟩, ⟨.assert0, .K, [.cur 22, gate.opd]⟩,
   ⟨.lin 1 0, .K, [.cur 11, .cur 15]⟩, ⟨.assert0, .K, [.cur 24, gate.opd]⟩]

/-- **The QLT loop** over `2^a` table entries. -/
def qltLoop (a qt lo m : Nat) (gate : Cell) : BM Unit := do
  let _ ← loop [a] (qltTpl qt lo m gate)
  pure ()

theorem unflat_one' {a jf : Nat} (h : jf < 2 ^ [a].sum) : unflat [a] jf = [jf] := by
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h
  simp [unflat, Nat.mod_eq_of_lt h]

theorem gpow_scale (l x : Nat) : gpow x + (gpow l + 1) * gpow x + 0 = gpow (x + l) := by
  rw [gpow_add, add_zero]
  have : gpow x + (gpow l + 1) * gpow x = gpow l * gpow x + (gpow x + gpow x) := by ring
  rw [this, FK.add_self, add_zero, mul_comm]

/-- A loop `readd` whose address operand holds `g^e` reads cell `e`. -/
theorem lreadd_spec {c : Ctx} {M : Mem} {o : LoopOut} {jf t lo m : Nat} {args : List Opd}
    (hr : o.tpl.getD t default = ⟨.readd lo m, .K, args⟩) (h : LRel c M o jf t) {N e : Nat}
    (hinj : GInj N) (hN : c.cells .K ≤ N) (he : e < N)
    (hα : ((args.getD 0 default).val M o jf).c₀ = gpow e) : (o.cell t jf).val M = FE.ofK (M.k e) := by
  obtain ⟨e', he', hx, hres⟩ := lrel_readd hr h
  rw [hα] at hx
  have := hinj e' e (by (clear * - hN he'; omega)) he hx
  subst this
  exact hres

/-- **The QLT loop's checks**: at every iteration whose table entry holds `α = g^e₁`, `β = g^e₂`
(addresses below `N`, `g`-powers injective below `N`), when the gate is `1`:
`mem[e₁] = v` and `mem[e₁ + 1 + l] = mem[e₂ + l]` for `l < 4`. -/
theorem qltLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {a qt lo m : Nat} {g : Nat}
    (h : SegsHold c M p (qltLoop a qt lo m (kc g) p).2) (hA : SegsAssert M p (qltLoop a qt lo m (kc g) p).2)
    (hg1 : M.k g = 1) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    {jf e₁ e₂ : Nat} (hjf : jf < 2 ^ a) (he₁ : e₁ + 5 ≤ N) (he₂ : e₂ + 4 ≤ N)
    (hα : M.k (qt + 3 * jf) = gpow e₁) (hβ : M.k (qt + 1 + 3 * jf) = gpow e₂) :
    M.k e₁ = M.k (qt + 2 + 3 * jf) ∧ ∀ l < 4, M.k (e₁ + 1 + l) = M.k (e₂ + l) := by
  simp only [qltLoop, hold_bind, assert_bind] at h hA
  have hj : jf < 2 ^ [a].sum := by simpa using hjf
  set o := (loop [a] (qltTpl qt lo m (kc g)) p).1 with ho
  have hR := fun t (ht : t < 26) => loop_rel h.1 hj (t := t) (by simp [qltTpl]; (clear * - ht; omega))
  have hS := fun t (ht : t < 26) => loop_assert hA.1 hj (t := t) (by simp [qltTpl]; (clear * - ht; omega))
  have hu : unflat o.dims jf = [jf] := unflat_one' hj
  -- the operand values
  have vα : (Opd.abs ⟨.K, qt, [3]⟩).val M o jf = FE.ofK (gpow e₁) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hα]
  have vβ : (Opd.abs ⟨.K, qt + 1, [3]⟩).val M o jf = FE.ofK (gpow e₂) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hβ]
  have vv : (Opd.abs ⟨.K, qt + 2, [3]⟩).val M o jf = FE.ofK (M.k (qt + 2 + 3 * jf)) := by
    rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]
  -- the addresses g^l·α, g^l·β
  have hadr : ∀ (t l e : Nat) (x : Opd), o.tpl.getD t default = ⟨.lin (gpow l + 1) 0, .K, [x, x]⟩ →
      x.val M o jf = FE.ofK (gpow e) → t < 26 → (o.cell t jf).val M = FE.ofK (gpow (e + l)) := by
    intro t l e x hr hx ht
    rw [lrel_lin hr (hR t ht)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hx, ofK_zero, add_zero]
    rw [← ofK_mul, ← ofK_add, ← gpow_scale l e, add_zero]
  have a1 := hadr 0 1 e₁ _ rfl vα (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have a2 := hadr 1 2 e₁ _ rfl vα (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have a3 := hadr 2 3 e₁ _ rfl vα (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have a4 := hadr 3 4 e₁ _ rfl vα (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have b1 := hadr 4 1 e₂ _ rfl vβ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have b2 := hadr 5 2 e₂ _ rfl vβ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have b3 := hadr 6 3 e₂ _ rfl vβ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  -- the reads
  have hrd : ∀ (t : Nat) (x : Opd) (e : Nat), o.tpl.getD t default = ⟨.readd lo m, .K, [x]⟩ →
      x.val M o jf = FE.ofK (gpow e) → e < N → t < 26 → (o.cell t jf).val M = FE.ofK (M.k e) := by
    intro t x e hr hx he ht
    exact lreadd_spec hr (hR t ht) hinj hN he (by simp [hx]; rfl)
  have r0 := hrd 7 _ e₁ rfl vα (by (clear * - he₁; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have r1 := hrd 8 (.cur 0) (e₁ + 1) rfl (by rw [Opd.val_cur _ _ hj]; exact a1) (by (clear * - he₁; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have r2 := hrd 9 (.cur 1) (e₁ + 2) rfl (by rw [Opd.val_cur _ _ hj]; exact a2) (by (clear * - he₁; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have r3 := hrd 10 (.cur 2) (e₁ + 3) rfl (by rw [Opd.val_cur _ _ hj]; exact a3) (by (clear * - he₁; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have r4 := hrd 11 (.cur 3) (e₁ + 4) rfl (by rw [Opd.val_cur _ _ hj]; exact a4) (by (clear * - he₁; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have s0 := hrd 12 _ e₂ rfl vβ (by (clear * - he₂; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have s1 := hrd 13 (.cur 4) (e₂ + 1) rfl (by rw [Opd.val_cur _ _ hj]; exact b1) (by (clear * - he₂; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have s2 := hrd 14 (.cur 5) (e₂ + 2) rfl (by rw [Opd.val_cur _ _ hj]; exact b2) (by (clear * - he₂; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  have s3 := hrd 15 (.cur 6) (e₂ + 3) rfl (by rw [Opd.val_cur _ _ hj]; exact b3) (by (clear * - he₂; omega)) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  -- the checks
  have hchk : ∀ (t : Nat) (x y : Opd) (X Y : FK), o.tpl.getD t default = ⟨.lin 1 0, .K, [x, y]⟩ →
      o.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, (kc g).opd]⟩ →
      x.val M o jf = FE.ofK X → y.val M o jf = FE.ofK Y → t + 1 < 26 → X = Y := by
    intro t x y X Y hr hr2 hx hy ht
    have hl := lrel_lin hr (hR t (by (clear * - ht; omega)))
    have ha := lassert_of hr2 (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ha
    rw [Cell.val_opd, Opd.val_cur _ _ hj, hl, hx, hy, Cell.val_K, hg1, ofK_one, one_mul,
      ofK_zero, add_zero, one_mul, ← ofK_add] at ha
    have := ofK_inj (ha.trans ofK_zero.symm)
    have e := congrArg (· + Y) this
    simpa [add_assoc, FK.add_self] using e
  refine ⟨hchk 16 (.cur 7) _ _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r0) vv (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), fun l hl => ?_⟩
  interval_cases l
  · exact hchk 18 (.cur 8) (.cur 12) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r1)
      (by rw [Opd.val_cur _ _ hj]; exact s0) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  · exact hchk 20 (.cur 9) (.cur 13) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r2)
      (by rw [Opd.val_cur _ _ hj]; exact s1) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  · exact hchk 22 (.cur 10) (.cur 14) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r3)
      (by rw [Opd.val_cur _ _ hj]; exact s2) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
  · exact hchk 24 (.cur 11) (.cur 15) _ _ rfl rfl (by rw [Opd.val_cur _ _ hj]; exact r4)
      (by rw [Opd.val_cur _ _ hj]; exact s3) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))

/-! ## Node queries -/

/-- A `K` word with the bits of `n` (not the field's `n`!). -/
def kOf (n : Nat) : FK := ⟨n.toUInt64⟩

/-- The rows of one lane `l` of a node check (rows `2 + 4l …`): `S = L + R`, `c = β·S + L`,
`d = c + P`, `z·d = 0`. -/
def nodeLane (L R P : Nat) (s : List Nat) (β g : Opd) (l : Nat) : List LRow :=
  [⟨.lin 1 0, .K, [.abs ⟨.K, L + l, s⟩, .abs ⟨.K, R + l, s⟩]⟩,
   ⟨.muladd, .K, [β, .cur (2 + 4 * l), .abs ⟨.K, L + l, s⟩]⟩,
   ⟨.lin 1 0, .K, [.cur (3 + 4 * l), .abs ⟨.K, P + l, s⟩]⟩,
   ⟨.assert0, .K, [.cur (4 + 4 * l), g]⟩]

/-- **The node template**: the length lane `len` is 64, and on each of the four lanes the previous
answer `P` is the half (`L` or `R`) the bit `β` selects; `z` gates every assertion. Lane operands move
with strides `s`, the bit with `sb`, the gate with `sz`. -/
def nodeTpl (len L R P : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (z : Nat) (sz : List Nat) : List LRow :=
  let β : Opd := .abs ⟨.K, bt, sb⟩
  let g : Opd := .abs ⟨.K, z, sz⟩
  [⟨.lin 0 (kOf 64), .K, [.abs ⟨.K, len, s⟩, .abs ⟨.K, len, s⟩]⟩, ⟨.assert0, .K, [.cur 0, g]⟩] ++
    nodeLane L R P s β g 0 ++ nodeLane L R P s β g 1 ++ nodeLane L R P s β g 2 ++ nodeLane L R P s β g 3

def nodeLoop (dims : List Nat) (len L R P : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (z : Nat)
    (sz : List Nat) : BM Unit := do
  let _ ← loop dims (nodeTpl len L R P s bt sb z sz)
  pure ()

theorem char2_eq {a b : FK} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h; simpa [add_assoc, FK.add_self] using this

/-- The value of an `assert0` row's gated check: `z·d = 0`, `z = 1` gives `d = 0`. -/
theorem gate_one {z d : FK} (h : FE.ofK z * FE.ofK d = 0) (hz : z = 1) : d = 0 := by
  rw [hz, ofK_one, one_mul, ← ofK_zero] at h; exact ofK_inj h

/-- **A node check**: with the gate `1` and the bit a bit, the length lane is 64 and each lane of the
previous answer is the selected half's. -/
theorem nodeLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {len L R P bt z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold c M p (nodeLoop dims len L R P s bt sb z sz p).2)
    (hA : SegsAssert M p (nodeLoop dims len L R P s bt sb z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hz : M.k (z + dot sz (unflat dims jf)) = 1)
    (hb : M.k (bt + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + dot sb (unflat dims jf)) = 1) :
    M.k (len + dot s (unflat dims jf)) = kOf 64 ∧ ∀ l < 4, M.k (P + l + dot s (unflat dims jf)) =
      if M.k (bt + dot sb (unflat dims jf)) = 1 then M.k (R + l + dot s (unflat dims jf))
      else M.k (L + l + dot s (unflat dims jf)) := by
  simp only [nodeLoop, hold_bind, assert_bind] at h hA
  have hR := fun t (ht : t < 18) => loop_rel h.1 hjf (t := t) (by simp [nodeTpl, nodeLane]; (clear * - ht; omega))
  have hS := fun t (ht : t < 18) => loop_assert hA.1 hjf (t := t) (by simp [nodeTpl, nodeLane]; (clear * - ht; omega))
  have hd : (loop dims (nodeTpl len L R P s bt sb z sz) p).1.dims = dims := rfl
  have vK : ∀ (b : Nat) (st : List Nat), (Opd.abs ⟨.K, b, st⟩).val M (loop dims (nodeTpl len L R P s bt sb z sz) p).1 jf = FE.ofK (M.k (b + dot st (unflat dims jf))) :=
    fun b st => by rw [Opd.val_absK, hd]
  have vc : ∀ t, (Opd.cur t).val M (loop dims (nodeTpl len L R P s bt sb z sz) p).1 jf = ((loop dims (nodeTpl len L R P s bt sb z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  -- a gated zero
  have hzero : ∀ t, t + 1 < 18 → (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, .abs ⟨.K, z, sz⟩]⟩ →
      ∀ X : FK, ((loop dims (nodeTpl len L R P s bt sb z sz) p).1.cell t jf).val M = FE.ofK X → X = 0 := by
    intro t ht hr X hX
    have := lassert_of hr (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, hX] at this
    exact gate_one this hz
  refine ⟨?_, fun l hl => ?_⟩
  · have h0 := lrel_lin (t := 0) rfl (hR 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, ofK_zero, zero_mul, add_zero] at h0
    rw [← ofK_add] at h0
    exact char2_eq (hzero 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) rfl _ h0)
  · have key : ∀ (lv : Nat), lv < 4 →
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (2 + 4 * lv) default = ⟨.lin 1 0, .K, [.abs ⟨.K, L + lv, s⟩, .abs ⟨.K, R + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (3 + 4 * lv) default = ⟨.muladd, .K, [.abs ⟨.K, bt, sb⟩, .cur (2 + 4 * lv), .abs ⟨.K, L + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (4 + 4 * lv) default = ⟨.lin 1 0, .K, [.cur (3 + 4 * lv), .abs ⟨.K, P + lv, s⟩]⟩ ∧
        (loop dims (nodeTpl len L R P s bt sb z sz) p).1.tpl.getD (4 + 4 * lv + 1) default = ⟨.assert0, .K, [.cur (4 + 4 * lv), .abs ⟨.K, z, sz⟩]⟩ := by
      intro lv hlv; interval_cases lv <;> exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := key l hl
    have e1 := lrel_lin k1 (hR _ (by (clear * - hl; omega)))
    have e2 := lrel_muladd k2 (hR _ (by (clear * - hl; omega)))
    have e3 := lrel_lin k3 (hR _ (by (clear * - hl; omega)))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_one, one_mul, ofK_zero, add_zero] at e1 e2 e3
    rw [e1] at e2; rw [e2] at e3
    rw [← ofK_add, ← ofK_mul, ← ofK_add, ← ofK_add] at e3
    have hd0 := hzero (4 + 4 * l) (by (clear * - hl; omega)) k4 _ e3
    have hP := (char2_eq hd0).symm
    rw [hP]
    rcases hb with h0 | h1
    · rw [h0]; simp [show (0 : FK) ≠ 1 from by decide]
    · rw [h1, if_pos rfl, one_mul]
      generalize M.k (L + l + dot s (unflat dims jf)) = a
      have : a + M.k (R + l + dot s (unflat dims jf)) + a = M.k (R + l + dot s (unflat dims jf)) + (a + a) := by ring
      rw [this, FK.add_self, add_zero]

/-! ## Cap checks -/

/-- The address chain's rows for bits `1 … c − 1`: per bit `z` (rows `2z + 1`, `2z + 2`)
`u = (G + 1)·acc`, `acc' = β_z·u + acc` with `G = g^(4 · 2^z)`. -/
def capChain (bt : Nat) (sb : List Nat) (c : Nat) : List LRow :=
  (List.range (c - 1)).flatMap fun y =>
    [⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩,
     ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]

/-- **The cap template** (per position): the leaf's length lane is the row length; the address
`α = g^(lo + 4 · Σ_z β_z 2^z)` from the `c` cap bits (row `2c`), `g^l·α`, four `readd`s, and the four
answer lanes `A + l` equal to them. Lane operands move with `s`, bits with `sb`, the gate with `sz`. -/
def capTpl (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat) (sz : List Nat) :
    List LRow :=
  let g : Opd := .abs ⟨.K, z, sz⟩
  let e := 2 * c
  [⟨.lin 0 (kOf row), .K, [.abs ⟨.K, lenL, s⟩, .abs ⟨.K, lenL, s⟩]⟩, ⟨.assert0, .K, [.cur 0, g]⟩,
   ⟨.lin (gpow lo * (gpow 4 + 1) + 1) (gpow lo), .K, [.abs ⟨.K, bt, sb⟩, .abs ⟨.K, bt, sb⟩]⟩] ++
  capChain bt sb c ++
  [⟨.lin (gpow 1 + 1) 0, .K, [.cur e, .cur e]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.readd rlo m, .K, [.cur e]⟩, ⟨.readd rlo m, .K, [.cur (e + 1)]⟩, ⟨.readd rlo m, .K, [.cur (e + 2)]⟩,
   ⟨.readd rlo m, .K, [.cur (e + 3)]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 8), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 10), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 12), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 14), g]⟩]

def capLoop (dims : List Nat) (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) : BM Unit := do
  let _ ← loop dims (capTpl lenL row A lo rlo m s bt sb c z sz)
  pure ()

theorem capChain_length (bt : Nat) (sb : List Nat) (c : Nat) : (capChain bt sb c).length = 2 * (c - 1) := by
  simp [capChain, List.length_flatMap]; ring

theorem capChain_getD (bt : Nat) (sb : List Nat) (c y : Nat) (hy : y + 1 < c) :
    (capChain bt sb c).getD (2 * y) default =
      ⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ ∧
    (capChain bt sb c).getD (2 * y + 1) default =
      ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩ := by
  suffices h : ∀ (n k y : Nat), y < n →
      ((List.range' k n).flatMap fun y : Nat =>
        [(⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ : LRow),
         ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]).getD (2 * y) default =
        ⟨.lin (gpow (4 * 2 ^ (k + y + 1))) 0, .K, [.cur (2 * (k + y + 1)), .cur (2 * (k + y + 1))]⟩ ∧
      ((List.range' k n).flatMap fun y : Nat =>
        [(⟨.lin (gpow (4 * 2 ^ (y + 1))) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ : LRow),
         ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]).getD (2 * y + 1) default =
        ⟨.muladd, .K, [.abs ⟨.K, bt + (k + y + 1), sb⟩, .cur (2 * (k + y + 1) + 1), .cur (2 * (k + y + 1))]⟩ by
    have := h (c - 1) 0 y (by (clear * - hy; omega))
    simpa [capChain, List.range_eq_range'] using this
  intro n
  induction n with
  | zero => intro k y hy; omega
  | succ n ih =>
    intro k y hy
    rw [List.range'_succ, List.flatMap_cons]
    rcases y with _ | y
    · simp
    · have := ih (k + 1) y (by (clear * - hy; omega))
      rw [show 2 * (y + 1) = 2 * y + 1 + 1 by ring, show 2 * y + 1 + 1 + 1 = 2 * y + 1 + 1 + 1 from rfl]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [show k + (y + 1) = k + 1 + y by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      exact this

/-- The number whose bit `y < n` is `1` iff cell `bt + y` (moved by `st` at `J`) holds `1`. -/
def bitSum (M : Mem) (bt : Nat) (st J : List Nat) (n : Nat) : Nat :=
  ((List.range n).map fun y => if M.k (bt + y + dot st J) = 1 then 2 ^ y else 0).sum

theorem bitSum_succ (M : Mem) (bt : Nat) (st J : List Nat) (n : Nat) :
    bitSum M bt st J (n + 1) = bitSum M bt st J n + (if M.k (bt + n + dot st J) = 1 then 2 ^ n else 0) := by
  simp [bitSum, List.range_succ]

theorem bitSum_lt (M : Mem) (bt : Nat) (st J : List Nat) : ∀ n, bitSum M bt st J n < 2 ^ n
  | 0 => by simp [bitSum]
  | n + 1 => by
    rw [bitSum_succ, Nat.pow_succ]; have := bitSum_lt M bt st J n
    split <;> (clear * - M bt st J n this; omega)

theorem getD_app3 {l₁ l₂ l₃ : List LRow} {i : Nat} :
    (l₁ ++ l₂ ++ l₃).getD (l₁.length + l₂.length + i) default = l₃.getD i default := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by (clear * - l₁ l₂ i; omega)),
    show l₁.length + l₂.length + i - l₁.length = l₂.length + i by (clear * - l₁ l₂ i; omega),
    List.getD_append_right _ _ _ _ (by (clear * - l₂ i; omega)), Nat.add_sub_cancel_left]

theorem getD_app2 {l₁ l₂ l₃ : List LRow} {i : Nat} (hi : i < l₂.length) :
    (l₁ ++ l₂ ++ l₃).getD (l₁.length + i) default = l₂.getD i default := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - l₁ i; omega))), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hi]

theorem capTpl_chain (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) {i : Nat} (hi : i < 2 * (c - 1)) :
    (capTpl lenL row A lo rlo m s bt sb c z sz).getD (3 + i) default = (capChain bt sb c).getD i default := by
  simp only [capTpl]
  exact getD_app2 (l₁ := [_, _, _]) (by rw [capChain_length]; exact hi)

/-- **A cap check**: with the gate `1`, Boolean cap bits and `GInj`, the leaf's length lane is the row
length and the four answer lanes are the cap node's lanes `lo + 4 · idx + l`, `idx` the bits' number. -/
theorem capLoop_spec {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2)
    (hA : SegsAssert M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hc : 1 ≤ c) (hz : M.k (z + dot sz (unflat dims jf)) = 1)
    (hb : ∀ y < c, M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1)
    {N : Nat} (hinj : GInj N) (hN : cx.cells .K ≤ N) (hlo : lo + 4 * 2 ^ c ≤ N) :
    M.k (lenL + dot s (unflat dims jf)) = kOf row ∧ ∀ l < 4, M.k (A + l + dot s (unflat dims jf)) =
      M.k (lo + 4 * bitSum M bt sb (unflat dims jf) c + l) := by
  simp only [capLoop, hold_bind, assert_bind] at h hA
  have hlen : (capTpl lenL row A lo rlo m s bt sb c z sz).length = 2 * c + 16 := by
    simp [capTpl, capChain_length]; (clear * - hc; omega)
  have hR := fun t (ht : t < 2 * c + 16) => loop_rel h.1 hjf (t := t) (by rw [hlen]; exact ht)
  have hS := fun t (ht : t < 2 * c + 16) => loop_assert hA.1 hjf (t := t) (by rw [hlen]; exact ht)
  generalize hJ : unflat dims jf = J at *
  have vK : ∀ (b : Nat) (st : List Nat),
      (Opd.abs ⟨.K, b, st⟩).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (M.k (b + dot st J)) := fun b st => by rw [Opd.val_absK]; show _ = FE.ofK (M.k (b + dot st J)); rw [← hJ]; rfl
  have vc : ∀ t, (Opd.cur t).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  have hzero : ∀ t, t + 1 < 2 * c + 16 →
      (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (t + 1) default =
        ⟨.assert0, .K, [.cur t, .abs ⟨.K, z, sz⟩]⟩ →
      ∀ X : FK, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M = FE.ofK X → X = 0 := by
    intro t ht hr X hX
    have := lassert_of hr (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, hX] at this
    exact gate_one this hz
  refine ⟨?_, ?_⟩
  · have h0 := lrel_lin (t := 0) rfl (hR 0 (by (clear * - hc; omega)))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, ofK_zero, zero_mul, add_zero] at h0
    rw [← ofK_add] at h0
    exact char2_eq (hzero 0 (by (clear * - hc; omega)) rfl _ h0)
  · -- the rows past the chain
    have hpost : ∀ i, (capTpl lenL row A lo rlo m s bt sb c z sz).getD (2 * c + 1 + i) default =
        ([⟨.lin (gpow 1 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.lin (gpow 3 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 1)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 2)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c + 3)]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 8), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 10), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 12), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 14), .abs ⟨.K, z, sz⟩]⟩] :
          List LRow).getD i default := by
      intro i
      have e : 2 * c + 1 + i = [(default : LRow), default, default].length + (capChain bt sb c).length + i := by
        simp [capChain_length]; (clear * - hc; omega)
      rw [e]; exact getD_app3
    -- the address chain
    have chain : ∀ y < c, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * y + 2) jf).val M =
        FE.ofK (gpow (lo + 4 * bitSum M bt sb J (y + 1))) := by
      intro y
      induction y with
      | zero =>
        intro _
        have h2 := lrel_lin (t := 2) rfl (hR 2 (by (clear * - hc; omega)))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK] at h2
        rw [h2, ← ofK_mul, ← ofK_add, ← ofK_add]
        congr 1
        rw [bitSum_succ, show bitSum M bt sb J 0 = 0 from rfl, Nat.zero_add, Nat.add_zero]
        rcases hb 0 hc with h0 | h1
        · simp only [Nat.add_zero] at h0; rw [h0]; simp [show (0 : FK) ≠ 1 from by decide, gpow]
        · simp only [Nat.add_zero] at h1
          rw [h1, if_pos rfl, mul_one]
          have e : (1 : FK) + (gpow lo * (gpow 4 + 1) + 1) + gpow lo =
              gpow lo * gpow 4 + ((1 + 1) + (gpow lo + gpow lo)) := by ring
          rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add]
          simp
      | succ y ih =>
        intro hy
        have ihv := ih (by (clear * - hy; omega))
        obtain ⟨k1, k2⟩ := capChain_getD bt sb c y hy
        have r1 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y) (by (clear * - hc hy; omega))
        have r2 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y + 1) (by (clear * - hc hy; omega))
        rw [k1] at r1; rw [k2] at r2
        rw [show 3 + 2 * y = 2 * y + 3 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)] at r1
        rw [show 3 + (2 * y + 1) = 2 * (y + 1) + 2 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)] at r2
        have e1 := lrel_lin r1 (hR _ (by (clear * - hy; omega)))
        have e2 := lrel_muladd r2 (hR _ (by (clear * - hy; omega)))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_zero, add_zero] at e1 e2
        rw [show 2 * (y + 1) = 2 * y + 2 by ring] at e1 e2
        rw [show 2 * y + 2 + 1 = 2 * y + 3 by ring] at e2
        rw [show 2 * (y + 1) + 2 = 2 * y + 2 + 2 by ring, e2, e1, ihv]
        simp only [← ofK_mul, ← ofK_add]
        congr 1
        have hsel := bit_select (gpow (lo + 4 * bitSum M bt sb J (y + 1))) (gpow (4 * 2 ^ (y + 1)))
          (M.k (bt + (y + 1) + dot sb J)) (hb (y + 1) hy)
        rw [add_zero] at hsel
        rw [hsel, bitSum_succ (n := y + 1)]
        split_ifs with hβ
        · rw [← gpow_add]; congr 1; ring
        · simp
    have hα0 := chain (c - 1) (by (clear * - hc; omega))
    rw [show 2 * (c - 1) + 2 = 2 * c by (clear * - hc; omega), show c - 1 + 1 = c by (clear * - hc; omega)] at hα0
    have hidx := bitSum_lt M bt sb J c
    generalize bitSum M bt sb J c = idx at hα0 hidx ⊢
    have hfour : lo + 4 * idx + 4 ≤ N := by
      have : 4 * idx + 4 ≤ 4 * 2 ^ c := by (clear * - hidx; omega)
      (clear * - hlo hidx; omega)
    -- g^l·α
    have sc : ∀ i < 3, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M = FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
      intro i hi
      have key : ∀ l, (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 1 + i) default = ⟨.lin (gpow l + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩ →
          l = i + 1 → ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M = FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
        intro l hr hl
        have e := lrel_lin hr (hR _ (by (clear * - hi hl; omega)))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vc, hα0, ofK_zero, add_zero] at e
        rw [e, ← ofK_mul, ← ofK_add, ← hl, ← gpow_scale l, add_zero]
      interval_cases i
      · exact key 1 (hpost 0) rfl
      · exact key 2 (hpost 1) rfl
      · exact key 3 (hpost 2) rfl
    have vcur : ∀ i < 4, (Opd.cur (2 * c + i)).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf = FE.ofK (gpow (lo + 4 * idx + i)) := by
      intro i hi
      rw [vc]
      rcases i with _ | i
      · simpa using hα0
      · have := sc i (by (clear * - hi; omega)); rw [show 2 * c + (i + 1) = 2 * c + 1 + i by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), this]
    -- the reads
    have rd : ∀ i < 4, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 4 + i) jf).val M = FE.ofK (M.k (lo + 4 * idx + i)) := by
      intro i hi
      have hr : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 4 + i) default = ⟨.readd rlo m, .K, [.cur (2 * c + i)]⟩ := by
        rw [show 2 * c + 4 + i = 2 * c + 1 + (3 + i) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        interval_cases i
        · exact hpost 3
        · exact hpost 4
        · exact hpost 5
        · exact hpost 6
      exact lreadd_spec hr (hR _ (by (clear * - hi; omega))) hinj hN (by (clear * - hfour hi; omega))
        (by rw [List.getD_cons_zero, vcur i hi]; rfl)
    intro l hl
    have hr1 : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l) default = ⟨.lin 1 0, .K, [.cur (2 * c + 4 + l), .abs ⟨.K, A + l, s⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l = 2 * c + 1 + (7 + 2 * l) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      interval_cases l
      · exact hpost 7
      · exact hpost 9
      · exact hpost 11
      · exact hpost 13
    have hr2 : (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l + 1) default = ⟨.assert0, .K, [.cur (2 * c + 8 + 2 * l), .abs ⟨.K, z, sz⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l + 1 = 2 * c + 1 + (8 + 2 * l) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      interval_cases l
      · exact hpost 8
      · exact hpost 10
      · exact hpost 12
      · exact hpost 14
    have e := lrel_lin hr1 (hR _ (by (clear * - hl; omega)))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vc, vK, rd l hl, ofK_one, one_mul, ofK_zero, add_zero] at e
    rw [← ofK_add] at e
    exact (char2_eq (hzero _ (by (clear * - hl; omega)) hr2 _ e)).symm

end Lvm.Loop.Build
end
-- ===== end of `LvmQLinkGadgets` =====

-- ===== merged from `LvmQLink` (GOLF module merge: `LvmQLink.lean` is now a stub importing `LvmQLinkSound`) =====
section
-- New for lvm (WP-11b-QL): the Q_link program (BLUEPRINT §4.6), written with LvmQBuild.

/-!
# Q_link: the stream is a trace of the schedule

Inputs (`Layout`): the stream lane `j` is the `K` cell `sb + j`; the node flag `fg`; the static
lane-check table **QLT** (`qt`, three cells per entry: `g^e₁`, `g^e₂`, `v`); the position bits
(`bb`, per opening a region of `H` cells per position, positions padded to their chunks); the
positions' BITS fields (`fl`: per position its low and its high field, A20).

Program (`qlink`), few loop blocks (A20: piece count binds):
0. the **position cells** (`posLoop`, A20): position `g` (all openings' positions in order) is the sum
   of its two BITS fields, `x_g = lo_g + hi_g` (`hi_g = 0` unless the position crosses a lane), the
   `K` cells `pt.k + g` that `Q_arith` reads (`eOfNat q`);
1. a **step array** (`stepArr`): `2^K` copies of the flag, then `2^K` zeros; a chunk of `r` real
   positions out of `2^a` is gated by `Z[2^K − r + j]`;
2. **the QLT loop** (`qltLoop`) over the table (`qltData`): lanes 0 and 1 (the constants), every
   FS entry (its length lane, and its first four lanes against its state entry's answer), and the
   last sponge block's padding lanes (WP-8's `PadOk`);
3. per opening, per position chunk: **cap loops** (the leaf's length lane; the last answer of the
   path against the cap node read at the address the cap bits give) and, per level chunk, **node
   loops** (the node's length lane; the previous answer in the half the position bit selects).

The soundness theorem is `LvmQLinkSound.qlink_sound`.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## The sponge padding (WP-8's `PadOk`, `padAt`, `nBlk`, verbatim, `rate = 136`) -/

/-- The number of Keccak-256 blocks of an `L`-byte message. -/
def nBlk (L : Nat) : Nat := L / 136 + 1

/-- The padding byte at offset `p` of a padded `L`-byte message (WP-8's `padAt`). -/
def padAt (L p : Nat) : UInt8 :=
  if p = L then (if L % 136 = 136 - 1 then 0x81 else 0x01)
  else if p % 136 = 136 - 1 then 0x80 else 0

/-- **The padding bytes of the stream are pinned** (WP-8's `PadOk` on the stream's bytes). -/
def PadOkB (B : List UInt8) (L : Nat) : Prop := ∀ q, L ≤ q → q < 136 * nBlk L → B.getD q 0 = padAt L q

/-- Lane `q` of the padding, as a number. -/
def padLane (L q : Nat) : Nat := ofLE ((List.range 8).map fun b => padAt L (8 * q + b))

/-! ## Layout and static data -/

/-- Where Q_link's inputs are. -/
structure Layout where
  /-- Stream lane `j` is the `K` cell `sb + j`. -/
  sb : Nat
  /-- The node flag cell. -/
  fg : Nat
  /-- The QLT table: entry `k` at cells `qt + 3k + {0, 1, 2}`. -/
  qt : Nat
  /-- The position bits: per opening, `H` cells per (padded) position. -/
  bb : Nat
  /-- `readd` region: the stream cells `[sb, sb + 2^m)`. -/
  m : Nat
  /-- The step array has `2^K` flags then `2^K` zeros. -/
  K : Nat
  /-- The QLT loop has `2^aQ` iterations. -/
  aQ : Nat
  /-- The positions' BITS fields: position `g`'s low field at `fl + g`, its high field at
  `fl + 2^pa + g`. -/
  fl : Nat
  /-- The positions loop has `2^pa` iterations. -/
  pa : Nat
  deriving Repr, Inhabited

/-- The positions chunks: the largest power of two, then the rest padded to a power of two. -/
def pchunks (t : Nat) : List (Nat × Nat) :=
  if t = 2 ^ t.log2 then [(0, t.log2)] else [(0, t.log2), (2 ^ t.log2, (t - 2 ^ t.log2 - 1).log2 + 1)]

/-- The positions an opening's bit region holds (its chunks, padded). -/
def padT (t : Nat) : Nat := ((pchunks t).map fun c => 2 ^ c.2).sum

/-- The QLT entries `(e₁, e₂, v)`: lanes 0, 1; every FS entry; the padding lanes. -/
def qltEntries (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  [(lay.sb, lay.sb + 1, lane0C), (lay.sb + 1, lay.sb + 2, lane1C)] ++
  ((plan p).zipIdx.filterMap fun x => match x.1.k with
    | .fs st => some (lay.sb + eLane p x.2, lay.sb + ansLane p st, x.1.len)
    | _ => none) ++
  ((List.range (17 * nBlk (hashedLen p) - hashedLen p / 8)).map fun k =>
    let q := hashedLen p / 8 + k
    (lay.sb + q, lay.sb + q + 1, padLane (hashedLen p) q))

/-- The QLT entries padded to `2^aQ` with copies of the first. -/
def qltPadded (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  qltEntries p lay ++ List.replicate (2 ^ lay.aQ - (qltEntries p lay).length) (lay.sb, lay.sb + 1, lane0C)

/-- The table cells of entries: per entry `g^e₁, g^e₂, v`. -/
def tblOf : List (Nat × Nat × Nat) → List FK
  | [] => []
  | e :: l => Build.gpow e.1 :: Build.gpow e.2.1 :: kOf e.2.2 :: tblOf l

/-- **The QLT input cells**: per entry `g^e₁, g^e₂, v`. -/
def qltData (p : Params) (lay : Layout) : List FK := tblOf (qltPadded p lay)

/-! ## The program -/

/-- The step array: `2^K` copies of the gate cell, then `2^K` zeros; returns its first cell. -/
def stepArr (K : Nat) (g : Cell) : BM Nat := do
  let pt ← getPtr
  let _ ← loop [K] [⟨.lin 0 0, .K, [g.opd, g.opd]⟩]
  let _ ← loop [K] [⟨.lin 1 0, .K, [g.opd, g.opd]⟩]
  pure pt.k

/-- The real positions of chunk `(s, a)` of an opening of `t` positions. -/
def realCount (t s a : Nat) : Nat := min (2 ^ a) (t - s)

/-- The loops of one opening (`zo` the step array, `bo` the opening's bit region). -/
def openLoops (p : Params) (lay : Layout) (zo bo : Nat) (o : OpenInfo) : BM Unit := do
  let L := o.L
  let ℓO := eLane p o.i0
  let Sj := posStride L
  let capL := eLane p o.ce + 1 + o.co / 8
  let _ ← seqAll ((pchunks L.t).map fun c => do
    let gz := zo + 2 ^ lay.K - realCount L.t c.1 c.2
    capLoop [c.2] (lay.sb + ℓO + Sj * c.1) L.row (lay.sb + ℓO + Sj * c.1 + slotOff L L.path + 9)
      (lay.sb + capL) lay.sb lay.m [Sj] (bo + L.height * c.1 + L.path) [L.height] (L.height - L.path) gz [1]
    let _ ← seqAll ((chunks L.path).map fun d =>
      nodeLoop [d.2, c.2] (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1))
        (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) + 1) (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) + 5)
        (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) - 4) [13, Sj]
        (bo + L.height * c.1 + d.1) [1, L.height] gz [0, 1])
    pure ())
  pure ()

/-- **The position cells** (A20): `2^a` rows `x_g = lo_g + hi_g`, the low fields from `lo`, the high
fields from `hi`. -/
def posLoop (a lo hi : Nat) : BM LoopOut :=
  loop [a] [⟨.lin 1 0, .K, [.abs ⟨.K, lo, [1]⟩, .abs ⟨.K, hi, [1]⟩]⟩]

/-- The index of position `j` of opening `k` among all positions (openings in order). -/
def posIdx (p : Params) (k j : Nat) : Nat := (((opens p).take k).map fun o => o.L.t).sum + j

/-- The bit region of opening `k` (the openings before it, padded). -/
def bitBase (p : Params) (lay : Layout) (k : Nat) : Nat :=
  lay.bb + (((opens p).take k).map fun o => padT o.L.t * o.L.height).sum

/-- Q_link after the position cells. -/
def qlinkCore (p : Params) (lay : Layout) : BM Unit := do
  let zo ← stepArr lay.K (kc lay.fg)
  qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)
  let _ ← seqAll ((List.range (opens p).length).map fun k =>
    openLoops p lay zo (bitBase p lay k) ((opens p).getD k default))
  pure ()

/-- **Q_link**: the position cells (at the start pointer's `K` cells), then the checks. -/
def qlink (p : Params) (lay : Layout) : BM Unit := do
  let _ ← posLoop lay.pa lay.fl (lay.fl + 2 ^ lay.pa)
  qlinkCore p lay

end Lvm.QLink
end
-- ===== end of `LvmQLink` =====

/-!
# Q_link is sound: its rows and assertions give `LaneLink` and the padding

`qlink_sound`: in any memory where Q_link's rows hold and its assertions hold (the committed memory
by `loopir_sound`, or the interpreter's), with the inputs where `Layout` says (`QIn`: the stream lanes,
the QLT table, the position bits from BITS, the flag `1`), the plan's static checks (`QOk`) and
`g`-powers injective below the cell counts, the stream meets every lane condition of the schedule
(`LaneLink`) and its last sponge block is padded (`PadOkB`, WP-8's `PadOk`).
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## Lanes as cells -/

/-- Stream lane `j` as a `K` value. -/
def laneK (ws : List Word) (j : Nat) : FK := ⟨UInt64.ofBitVec (ws.getD j 0)⟩

theorem laneK_val (ws : List Word) (j : Nat) : (laneK ws j).val.toNat = lw ws j := rfl

theorem lw_of_laneK {ws : List Word} {j j' : Nat} (h : laneK ws j = laneK ws j') : lw ws j = lw ws j' := by
  rw [← laneK_val, h, laneK_val]

theorem kOf_toNat {v : Nat} (hv : v < 2 ^ 64) : (kOf v).val.toNat = v := by
  have : v < 18446744073709551616 := lt_of_lt_of_eq hv (by norm_num)
  simp [kOf, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt this]

theorem lw_of_kOf {ws : List Word} {j v : Nat} (hv : v < 2 ^ 64) (h : laneK ws j = kOf v) : lw ws j = v := by
  rw [← laneK_val, h, kOf_toNat hv]

/-! ## Extracting a gadget's rows from a program -/

theorem seqAll_both {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)) (p : Ptr), SegsHold c M p (seqAll ms p).2 → SegsAssert M p (seqAll ms p).2 →
      ∀ m ∈ ms, ∃ q, SegsHold c M q (m q).2 ∧ SegsAssert M q (m q).2
  | [], _, _, _, _, h => by simp at h
  | m :: ms, p, h, hA, m', hm => by
    simp only [seqAll] at h hA
    rw [hold_bind] at h; rw [assert_bind] at hA
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨p, h.1, hA.1⟩
    · rw [hold_bind] at h; rw [assert_bind] at hA
      exact seqAll_both ms _ h.2.1 hA.2.1 m' hm

/-! ## The step array -/

theorem stepArr_apply (K : Nat) (g : Cell) (p : Ptr) :
    (stepArr K g p).1 = p.k := rfl

theorem stepArr_spec {c : Ctx} {M : Mem} {p : Ptr} {K g : Nat} (h : SegsHold c M p (stepArr K (kc g) p).2) :
    (∀ x < 2 ^ K, M.k (p.k + x) = M.k g) ∧ (∀ x < 2 ^ K, M.k (p.k + 2 ^ K + x) = 0) := by
  simp only [stepArr] at h
  rw [hold_bind] at h
  obtain ⟨-, h⟩ := h
  simp only [getPtr, Ptr.adv_nil] at h
  rw [hold_bind] at h
  obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨h2, -⟩ := h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have e := lrel_lin (t := 0) rfl (loop_rel h1 (jf := x) (by simpa using hx) (by simp))
    simp only [List.getD_cons_zero, List.getD_cons_succ, Cell.val_opd, Cell.val_K, ofK_zero, zero_mul,
      add_zero, LoopOut.cell_val] at e
    simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
      List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at] at e
    simpa [Mem.rd] using ofK_inj e
  · have e := lrel_lin (t := 0) rfl (loop_rel h2 (jf := x) (by simpa using hx) (by simp))
    simp only [List.getD_cons_zero, List.getD_cons_succ, Cell.val_opd, Cell.val_K, ofK_one, one_mul,
      ofK_zero, add_zero, LoopOut.cell_val] at e
    simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
      List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at, Ptr.adv, segsW, Seg.w, Block.tw,
      Block.size, Block.lsize, mkLoop] at e
    rw [← ofK_add, FK.add_self] at e
    simpa [Mem.rd, Nat.add_assoc] using ofK_inj e

/-! ## Inputs and static conditions -/

/-- **Where Q_link's inputs are**, and the flag. -/
structure QIn (p : Params) (lay : Layout) (ws : List Word) (M : Mem) : Prop where
  /-- The node flag is on. -/
  flag : M.k lay.fg = 1
  /-- The stream region holds the stream's lanes. -/
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK ws j
  /-- The QLT table. -/
  table : ∀ x < (qltData p lay).length, M.k (lay.qt + x) = (qltData p lay).getD x 0
  /-- The position bits (BITS): bit `z` of position `j` of opening `k`. -/
  bits : ∀ k < (opens p).length, ∀ j < ((opens p).getD k default).L.t,
    ∀ z < ((opens p).getD k default).L.height,
    M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) =
      if ansBit p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height + z)
      then 1 else 0

/-- **Q_link's static conditions** (decided per parameter set and layout). -/
structure QOk (p : Params) (lay : Layout) : Prop where
  qlen : (qltEntries p lay).length ≤ 2 ^ lay.aQ
  qbound : ∀ e ∈ qltEntries p lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
    e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64
  hT : hashedLen p / 8 + 17 ≤ 2 ^ lay.m
  opens : ∀ o ∈ opens p, 1 ≤ o.L.path ∧ o.L.path < o.L.height ∧ (∀ c ∈ pchunks o.L.t, c.2 ≤ lay.K) ∧
    eLane p o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m ∧ o.L.row < 2 ^ 64
  /-- The position cells cover every position. -/
  pos : ((Lvm.QLink.opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa

theorem qltPadded_length (p : Params) (lay : Layout) (h : (qltEntries p lay).length ≤ 2 ^ lay.aQ) :
    (qltPadded p lay).length = 2 ^ lay.aQ := by
  simp [qltPadded]; (clear * - p lay h; omega)

theorem tblOf_length : ∀ l : List (Nat × Nat × Nat), (tblOf l).length = 3 * l.length
  | [] => rfl
  | _ :: l => by simp [tblOf, tblOf_length l]; ring

theorem tblOf_getD : ∀ (l : List (Nat × Nat × Nat)) {k : Nat}, k < l.length →
      (tblOf l).getD (3 * k) 0 = Build.gpow (l.getD k (0, 0, 0)).1 ∧
      (tblOf l).getD (3 * k + 1) 0 = Build.gpow (l.getD k (0, 0, 0)).2.1 ∧
      (tblOf l).getD (3 * k + 2) 0 = kOf (l.getD k (0, 0, 0)).2.2
  | [], _, hk => by simp at hk
  | e :: l, 0, _ => by simp [tblOf]
  | e :: l, k + 1, hk => by
    have := tblOf_getD l (k := k) (by simpa using hk)
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, show 3 * k + 1 + 1 + 1 + 1 = 3 * k + 1 + 1 + 1 + 1 from rfl,
      show 3 * k + 1 + 1 + 1 + 2 = 3 * k + 2 + 1 + 1 + 1 by ring]
    simp only [tblOf, List.getD_cons_succ, Nat.add_assoc] at this ⊢
    exact this

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Every QLT entry's checks hold.** -/
theorem qlt_entry (hQ : QOk p lay) (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    (hA : SegsAssert M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    {e : Nat × Nat × Nat} (he : e ∈ qltEntries p lay) :
    M.k e.1 = kOf e.2.2 ∧ ∀ l < 4, M.k (e.1 + 1 + l) = M.k (e.2.1 + l) := by
  have hmem : e ∈ qltPadded p lay := List.mem_append_left _ he
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hmem
  rw [qltPadded_length p lay hQ.qlen] at hk
  have hkd : (qltPadded p lay).getD k (0, 0, 0) = e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [qltPadded_length p lay hQ.qlen]; exact hk)]
    simpa using hke
  have hd := tblOf_getD (qltPadded p lay) (k := k) (by rw [qltPadded_length p lay hQ.qlen]; exact hk)
  rw [hkd] at hd
  have hlenD : (qltData p lay).length = 3 * 2 ^ lay.aQ := by
    rw [qltData, tblOf_length, qltPadded_length p lay hQ.qlen]
  have t0 := hin.table (3 * k) (by (clear * - hk hlenD; omega))
  have t1 := hin.table (3 * k + 1) (by (clear * - hk hlenD; omega))
  have t2 := hin.table (3 * k + 2) (by (clear * - hk hlenD; omega))
  simp only [qltData] at t0 t1 t2
  rw [hd.1] at t0; rw [hd.2.1] at t1; rw [hd.2.2] at t2
  obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound e he
  have := qltLoop_spec h hA hin.flag hinj hN (jf := k) (e₁ := e.1) (e₂ := e.2.1) hk (by (clear * - hNs b3; omega)) (by (clear * - hNs b4; omega))
    t0 (by rw [show lay.qt + 1 + 3 * k = lay.qt + (3 * k + 1) by ring]; exact t1)
  rw [show lay.qt + 2 + 3 * k = lay.qt + (3 * k + 2) by ring, t2] at this
  exact this

end

/-! ## Openings -/

theorem unflat_two' {dc dx c y : Nat} (hc : c < 2 ^ dc) (hy : y < 2 ^ dx) :
    unflat [dc, dx] (c + 2 ^ dc * y) = [c, y] := by
  have hm : (c + 2 ^ dc * y) % 2 ^ dc = c := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hdv : (c + 2 ^ dc * y) / 2 ^ dc = y := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hc, Nat.zero_add]
  simp [unflat, hm, hdv, Nat.mod_eq_of_lt hy]

theorem pchunks_cover {t j : Nat} (hj : j < t) :
    ∃ c ∈ pchunks t, c.1 ≤ j ∧ j - c.1 < realCount t c.1 c.2 ∧ j - c.1 < 2 ^ c.2 := by
  have ht : t ≠ 0 := by (clear * - t j hj; omega)
  have h1 := Nat.log2_self_le ht
  have h2 := @Nat.lt_log2_self t
  unfold pchunks realCount
  split
  · next he => exact ⟨(0, t.log2), by simp, by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t j; omega)), by simp; (clear * - hj he; omega), by simp; (clear * - hj he; omega)⟩
  · next he =>
    by_cases hj2 : j < 2 ^ t.log2
    · exact ⟨(0, t.log2), by simp, by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t j; omega)), by simp; (clear * - hj hj2; omega), by simp; omega⟩
    · have h3 := @Nat.lt_log2_self (t - 2 ^ t.log2 - 1)
      refine ⟨(2 ^ t.log2, (t - 2 ^ t.log2 - 1).log2 + 1), by simp, by simp; (clear * - hj2; omega), ?_, ?_⟩ <;> simp <;> (clear * - hj h1 hj2 h3; omega)

theorem realCount_le (t s a : Nat) : realCount t s a ≤ 2 ^ a := Nat.min_le_left _ _

theorem bitSum_congr (M : Mem) (bt bt' : Nat) (st st' J J' : List Nat) (n : Nat)
    (h : ∀ y < n, bt + y + Loop.dot st J = bt' + y + Loop.dot st' J') : bitSum M bt st J n = bitSum M bt' st' J' n := by
  simp only [bitSum]
  congr 1
  exact List.map_congr_left fun y hy => by rw [h y (by simpa using hy)]

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **An opening's checks hold at every position.** -/
theorem open_facts (hQ : QOk p lay) (hin : QIn p lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < (opens p).length) {o : OpenInfo} (hko : (opens p).getD k default = o) {q : Ptr}
    (h : SegsHold c M q (openLoops p lay zo (bitBase p lay k) o q).2)
    (hA : SegsAssert M q (openLoops p lay zo (bitBase p lay k) o q).2)
    {j : Nat} (hj : j < o.L.t) :
    M.k (lay.sb + eLane p o.i0 + posStride o.L * j) = kOf o.L.row ∧
    (∀ l < 4, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L o.L.path + 9 + l) =
      M.k (lay.sb + (eLane p o.ce + 1 + o.co / 8) +
        4 * bitSum M (bitBase p lay k + o.L.height * j + o.L.path) [] [] (o.L.height - o.L.path) + l)) ∧
    (∀ lvl < o.L.path, M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1)) = kOf 64 ∧ ∀ l < 4,
      M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) - 4 + l) =
        if M.k (bitBase p lay k + o.L.height * j + lvl) = 1 then M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 5 + l)
        else M.k ((lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 1 + l)) := by
  have ho : o ∈ opens p := by
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1, hph, hK, hcap, hrow⟩ := hQ.opens o ho
  have hbit : ∀ j' < o.L.t, ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * j' + z) = 0 ∨
      M.k (bitBase p lay k + o.L.height * j' + z) = 1 := by
    intro j' hj' z hz'
    have := hin.bits k hk j' (by rw [hko]; exact hj') z (by rw [hko]; exact hz')
    rw [hko] at this
    rw [this]; split <;> simp
  simp only [openLoops] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨cc, hcc, hc1, hc2, hc3⟩ := pchunks_cover hj
  obtain ⟨q1, h1, hA1⟩ := seqAll_both _ _ h.1 hA.1 _ (List.mem_map_of_mem hcc)
  rw [hold_bind] at h1; rw [assert_bind] at hA1
  have hgate : ∀ jj, jj < realCount o.L.t cc.1 cc.2 →
      M.k (zo + 2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj) = 1 := by
    intro jj hjj
    have hr := realCount_le o.L.t cc.1 cc.2
    have hKc : 2 ^ cc.2 ≤ 2 ^ lay.K := Nat.pow_le_pow_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (hK cc hcc)
    rw [show zo + 2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj = zo + (2 ^ lay.K - realCount o.L.t cc.1 cc.2 + jj) by (clear * - hr hKc; omega)]
    exact hz _ (by (clear * - hjj hr hKc; omega))
  have hjs : j = cc.1 + (j - cc.1) := by (clear * - hc1; omega)
  have hHj : o.L.height * j = o.L.height * cc.1 + o.L.height * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  have hSj : posStride o.L * j = posStride o.L * cc.1 + posStride o.L * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  -- the cap loop
  have hc' := capLoop_spec h1.1 hA1.1 (jf := j - cc.1) (by simpa using hc3) (by (clear * - hph; omega))
    (by simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero, Nat.one_mul]
        exact hgate _ hc2)
    (fun y hy => by
      simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero]
      have := hbit j hj (o.L.path + y) (by (clear * - hph hy; omega))
      rwa [show bitBase p lay k + o.L.height * cc.1 + o.L.path + y + o.L.height * (j - cc.1) =
        bitBase p lay k + o.L.height * j + (o.L.path + y) by (clear * - hHj; omega)])
    hinj hN (by (clear * - hNs hcap; omega))
  simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero] at hc'
  have hbase : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + posStride o.L * (j - cc.1) = (lay.sb + eLane p o.i0 + posStride o.L * j) := by
    (clear * - hSj; omega)
  refine ⟨?_, fun l hl => ?_, fun lvl hlvl => ?_⟩
  · rw [← hbase]; exact hc'.1
  · have := hc'.2 l hl
    rw [show lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L o.L.path + 9 + l +
        posStride o.L * (j - cc.1) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L o.L.path + 9 + l by (clear * - hSj; omega)] at this
    rw [this, bitSum_congr M _ (bitBase p lay k + o.L.height * j + o.L.path) [o.L.height] [] [j - cc.1] []
      (o.L.height - o.L.path) (fun y _ => by simp only [Loop.dot]; (clear * - hHj; omega))]
  · -- the node loop of the level chunk holding lvl
    obtain ⟨dd, hdd, hd1, hd2⟩ := chunks_cover hlvl
    have h1s := h1.2; have hA1s := hA1.2
    rw [hold_bind] at h1s; rw [assert_bind] at hA1s
    obtain ⟨q2, h2, hA2⟩ := seqAll_both _ _ h1s.1 hA1s.1 _ (List.mem_map_of_mem hdd)
    have hjf : lvl - dd.1 + 2 ^ dd.2 * (j - cc.1) < 2 ^ [dd.2, cc.2].sum := by
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_add]
      have := Nat.mul_le_mul_left (2 ^ dd.2) (show j - cc.1 + 1 ≤ 2 ^ cc.2 by (clear * - hc3; omega))
      rw [Nat.mul_add, Nat.mul_one] at this; (clear * - hd1 hd2 this; omega)
    have hu := unflat_two' (dc := dd.2) (dx := cc.2) (c := lvl - dd.1) (y := j - cc.1) (by (clear * - hd1 hd2; omega)) hc3
    have hn := nodeLoop_spec h2 hA2 hjf
      (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.zero_mul, Nat.zero_add, Nat.one_mul]; exact hgate _ hc2)
      (by rw [hu]; simp only [Loop.dot, Nat.add_zero, Nat.one_mul]
          have := hbit j hj lvl (by (clear * - hph hlvl; omega))
          rwa [show bitBase p lay k + o.L.height * cc.1 + dd.1 + (lvl - dd.1 + o.L.height * (j - cc.1)) =
            bitBase p lay k + o.L.height * j + lvl by (clear * - hHj hd1; omega)])
    rw [hu] at hn
    simp only [Loop.dot, Nat.add_zero] at hn
    have hsl : slotOff o.L (dd.1 + 1) + 13 * (lvl - dd.1) = slotOff o.L (lvl + 1) := by
      simp only [slotOff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]; (clear * - hd1; omega)
    have hb2 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) := by
      (clear * - hSj hsl; omega)
    have hbit' : bitBase p lay k + o.L.height * cc.1 + dd.1 + (1 * (lvl - dd.1) + o.L.height * (j - cc.1)) =
        bitBase p lay k + o.L.height * j + lvl := by (clear * - hHj hd1; omega)
    refine ⟨by rw [← hb2]; exact hn.1, fun l hl => ?_⟩
    have := hn.2 l hl
    have e1 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) - 4 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) - 4 + l := by
      have : 4 ≤ lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) := by
        simp only [slotOff, Nat.add_one_ne_zero, ite_false]; (clear * - hrow; omega)
      (clear * - hSj hsl this; omega)
    have e2 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) + 5 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 5 + l := by (clear * - hSj hsl; omega)
    have e3 : lay.sb + eLane p o.i0 + posStride o.L * cc.1 + slotOff o.L (dd.1 + 1) + 1 + l +
        (13 * (lvl - dd.1) + posStride o.L * (j - cc.1)) = (lay.sb + eLane p o.i0 + posStride o.L * j) + slotOff o.L (lvl + 1) + 1 + l := by (clear * - hSj hsl; omega)
    simp only [hbit', e1, e2, e3] at this
    exact this

end

/-! ## The theorem -/

theorem byte_of_lane (ws : List Word) (q b : Nat) (hb : b < 8) :
    (wordsBytes ws).getD (8 * q + b) 0 = ((lw ws q) / 256 ^ b % 256).toUInt8 := by
  rw [← wordByte_eq_getD, wordByte, show (8 * q + b) / 8 = q by (clear * - q b hb; omega), show (8 * q + b) % 8 = b by (clear * - q b hb; omega),
    ← toUInt8_mod]
  rfl

theorem padLane_byte (L q b : Nat) (hb : b < 8) : (padLane L q / 256 ^ b % 256).toUInt8 = padAt L (8 * q + b) := by
  rw [padLane, ofLE_div_mod]
  simp [List.getD_eq_getElem?_getD, hb]

theorem fk01 : ¬ ((0 : FK) = 1) := by decide

theorem posL_succ (p : Params) (ws : List Word) (e s h : Nat) :
    posL p ws e s (h + 1) = posL p ws e s h + (if ansBit p ws e (s + h) then 2 ^ h else 0) := by
  simp [posL, List.range_succ]

theorem posL_lt (p : Params) (ws : List Word) (e s : Nat) : ∀ h, posL p ws e s h < 2 ^ h
  | 0 => by simp [posL]
  | h + 1 => by
    rw [posL_succ, Nat.pow_succ]; have := posL_lt p ws e s h
    split <;> (clear * - p ws e s h this; omega)

theorem bitSum_posL {p : Params} {ws : List Word} {M : Mem} {bt e s n : Nat}
    (hb : ∀ y < n, M.k (bt + y) = if ansBit p ws e (s + y) then 1 else 0) :
    bitSum M bt [] [] n = posL p ws e s n := by
  simp only [bitSum, posL]
  congr 1
  apply List.map_congr_left
  intro y hy
  rw [show bt + y + Loop.dot [] [] = bt + y from rfl, hb y (List.mem_range.mp hy)]
  split <;> simp [fk01]

theorem lanes_in {p : Params} (hS : StreamOk p) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    eLane p i + 5 + ((plan p).getD i default).len / 8 ≤ hashedLen p / 8 := by
  have e := entry_end p hi
  rw [← hS.2, bOff_eq hS.1 h1 (by (clear * - hi; omega))] at e
  have := streamOk_len hS.1 h1 hi
  (clear * - e this; omega)

/-- An opening entry: its opening, position and slot. -/
theorem open_pos {p : Params} {i : Nat} (hi : i < (plan p).length)
    (he : ((plan p).getD i default).k.isOpen = true) :
    ∃ k, k < (opens p).length ∧ ∃ o, (opens p).getD k default = o ∧ ∃ jj y, jj < o.L.t ∧ y < 1 + o.L.path ∧
      i = o.i0 + jj * (1 + o.L.path) + y ∧
      (plan p).getD i default = if y = 0 then ⟨.leaf, o.L.row⟩
        else ⟨.node o.pe o.L.height jj (y - 1) (if y = o.L.path then some (o.ce, o.co, o.L.path) else none), 64⟩ := by
  obtain ⟨o, ho, h1, h2, h3⟩ := open_of_entry p hi he
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  rw [openPlan_length] at h2
  have hP : 0 < 1 + o.L.path := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - o; omega))
  have hx : (i - o.i0) / (1 + o.L.path) * (1 + o.L.path) + (i - o.i0) % (1 + o.L.path) = i - o.i0 :=
    Nat.div_add_mod' _ _
  have hjt : (i - o.i0) / (1 + o.L.path) < o.L.t := by
    rw [Nat.div_lt_iff_lt_mul hP]; (clear * - h1 h2; omega)
  have e := openPlan_getD o.L o.pe o.ce o.co hjt (Nat.mod_lt (i - o.i0) hP)
  rw [hx] at e
  refine ⟨k, hk, o, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hko],
    (i - o.i0) / (1 + o.L.path), (i - o.i0) % (1 + o.L.path), hjt, Nat.mod_lt _ hP, by (clear * - h1 hx; omega), ?_⟩
  rw [h3, e]

section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

-- B1-IX: the typed schedule's concrete prefix (`LvmSchedule.phases`) makes the unifier unfold `opens p` to its
-- items; nothing here needs it unfolded
attribute [local irreducible] Lvm.schedule in
/-- Q_link's checks after the position cells. -/
theorem qlinkCore_sound (hS : StreamOk p) (hQ : QOk p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlinkCore p lay pt).2) (hA : SegsAssert M pt (qlinkCore p lay pt).2) :
    LaneLink p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlinkCore] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨hz1, -⟩ := stepArr_spec h.1
  have hz : ∀ x < 2 ^ lay.K, M.k (pt.k + x) = 1 := fun x hx => by rw [hz1 x hx, hin.flag]
  have h2 := h.2; have hA2 := hA.2
  rw [stepArr_apply] at h2 hA2
  rw [hold_bind] at h2; rw [assert_bind] at hA2
  have QE : ∀ a b v, (a, b, v) ∈ qltEntries p lay → M.k a = kOf v ∧ ∀ l < 4, M.k (a + 1 + l) = M.k (b + l) :=
    fun a b v he => qlt_entry hQ hin hinj hN hNs h2.1 hA2.1 he
  have QB : ∀ a b v, (a, b, v) ∈ qltEntries p lay → lay.sb ≤ a ∧ lay.sb ≤ b ∧ a + 5 ≤ lay.sb + 2 ^ lay.m ∧
      b + 4 ≤ lay.sb + 2 ^ lay.m ∧ v < 2 ^ 64 := fun a b v he => hQ.qbound _ he
  have h3 := h2.2; have hA3 := hA2.2
  rw [hold_bind] at h3; rw [assert_bind] at hA3
  have hopk : ∀ k, k < (opens p).length → ∀ o, (opens p).getD k default = o →
      ∃ q, SegsHold c M q (openLoops p lay pt.k (bitBase p lay k) o q).2 ∧
        SegsAssert M q (openLoops p lay pt.k (bitBase p lay k) o q).2 := by
    intro k hk o hko
    obtain ⟨q, hq1, hq2⟩ := seqAll_both _ _ h3.1 hA3.1 _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    subst hko
    exact ⟨q, hq1, hq2⟩
  -- stream lanes
  have hT := hQ.hT
  have hL8 : hashedLen p % 8 = 0 := by
    have := bOff_mod hS.1 (plan p).length (by have := plan_length_ge p; (clear * - this; omega)) le_rfl
    rw [bOff_end, ← hS.2] at this; exact this
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  -- FS entries are QLT entries
  have FSM : ∀ i, i < (plan p).length → ∀ st, ((plan p).getD i default).k = .fs st →
      (lay.sb + eLane p i, lay.sb + ansLane p st, ((plan p).getD i default).len) ∈ qltEntries p lay := by
    intro i hi st hk
    have hgi : (plan p).getD i default = (plan p)[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [hgi] at hk ⊢
    apply List.mem_append_left; apply List.mem_append_right
    rw [List.mem_filterMap]
    exact ⟨((plan p)[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]),
      by simp only [hk]⟩
  -- opening entries
  have OE : ∀ i, i < (plan p).length → ((plan p).getD i default).k.isOpen = true →
      ∃ k o jj y, k < (opens p).length ∧ (opens p).getD k default = o ∧ jj < o.L.t ∧ y < 1 + o.L.path ∧
        (plan p).getD i default = (if y = 0 then ⟨.leaf, o.L.row⟩ else ⟨.node o.pe o.L.height jj (y - 1)
          (if y = o.L.path then some (o.ce, o.co, o.L.path) else none), 64⟩) ∧
        lw ws (eLane p i) = ((plan p).getD i default).len ∧
        (y ≠ 0 → ∀ l < 4, lw ws ((if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1))
          then eLane p i + 5 else eLane p i + 1) + l) = lw ws (eLane p i - 4 + l)) ∧
        (y = o.L.path → ∀ l < 4, lw ws (eLane p i + 9 + l) = lw ws (eLane p o.ce + 1 + o.co / 8 +
          4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) + l)) := by
    intro i hi he
    obtain ⟨k, hk, o, hko, jj, y, hjj, hy, hieq, hpe⟩ := open_pos hi he
    have ho : o ∈ opens p := by
      rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
    obtain ⟨q, hq1, hq2⟩ := hopk k hk o hko
    obtain ⟨f1, f2, f3⟩ := open_facts hQ hin hinj hN hNs hz hk hko hq1 hq2 hjj
    have hEL : eLane p i = eLane p o.i0 + posStride o.L * jj + slotOff o.L y := by
      rw [hieq, eLane_open hS ho hjj (by (clear * - hy; omega)), Nat.mul_comm]
    have hi1 : 1 ≤ i := by have := opens_i0 p ho; (clear * - hieq this; omega)
    have hin_ := lanes_in hS hi1 hi
    have hbits : ∀ z < o.L.height, M.k (bitBase p lay k + o.L.height * jj + z) =
        if ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + z) then 1 else 0 := by
      intro z hz
      have := hin.bits k hk jj (by rw [hko]; exact hjj) z (by rw [hko]; exact hz)
      rw [hko] at this; exact this
    obtain ⟨hp1, hph, -, hcapb, hrow⟩ := hQ.opens o ho
    refine ⟨k, o, jj, y, hk, hko, hjj, hy, hpe, ?_, ?_, ?_⟩
    · by_cases hy0 : y = 0
      · subst hy0
        rw [hpe, if_pos rfl]
        rw [hpe, if_pos rfl] at hin_
        refine LV _ _ (by (clear * - hT hin_ hEL; omega)) hrow ?_
        rw [hEL, show lay.sb + (eLane p o.i0 + posStride o.L * jj + slotOff o.L 0) =
          lay.sb + eLane p o.i0 + posStride o.L * jj by simp [slotOff]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        exact f1
      · rw [hpe, if_neg hy0]
        rw [hpe, if_neg hy0] at hin_
        have := (f3 (y - 1) (by (clear * - hy hp1; omega))).1
        rw [show y - 1 + 1 = y by (clear * - hy0; omega)] at this
        refine LV _ _ (by (clear * - hT hEL hin_; omega)) (by norm_num) ?_
        rw [hEL, show lay.sb + (eLane p o.i0 + posStride o.L * jj + slotOff o.L y) =
          lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        exact this
    · intro hy0 l hl
      have e := (f3 (y - 1) (by (clear * - hy hp1; omega))).2 l hl
      rw [show y - 1 + 1 = y by (clear * - hy0; omega)] at e
      have hs5 : 5 ≤ slotOff o.L y := by simp only [slotOff, if_neg hy0]; (clear * - hrow; omega)
      have hb := hbits (y - 1) (by (clear * - hy hp1 hph; omega))
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane p i + 13 ≤ hashedLen p / 8 := by simp only at hin_; (clear * - hin_; omega)
      by_cases hab : ansBit p ws (o.pe + jj / 8) (jj % 8 * o.L.height + (y - 1)) = true
      · rw [if_pos hab] at hb ⊢; rw [if_pos hb] at e
        refine (LE _ _ (by (clear * - hT hL8 hEL hl h13; omega)) (by (clear * - hT hEL hin_ hl; omega)) ?_).symm
        rw [show lay.sb + (eLane p i - 4 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y - 4 + l
            by (clear * - hEL hs5; omega),
          show lay.sb + (eLane p i + 5 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y + 5 + l
            by (clear * - hEL; omega)]
        exact e
      · rw [if_neg hab] at hb ⊢; rw [hb, if_neg fk01] at e
        refine (LE _ _ (by (clear * - hT hL8 hEL hl h13; omega)) (by (clear * - hT hEL hin_ hl; omega)) ?_).symm
        rw [show lay.sb + (eLane p i - 4 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y - 4 + l
            by (clear * - hEL hs5; omega),
          show lay.sb + (eLane p i + 1 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L y + 1 + l
            by (clear * - hEL; omega)]
        exact e
    · intro hyp l hl
      subst hyp
      have e := f2 l hl
      have hbs : bitSum M (bitBase p lay k + o.L.height * jj + o.L.path) [] [] (o.L.height - o.L.path) =
          posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) :=
        bitSum_posL fun z hz => by
          have := hbits (o.L.path + z) (by (clear * - hph hz; omega))
          simpa only [Nat.add_assoc] using this
      rw [hbs] at e
      have hpl := posL_lt p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path)
      have hy0 : o.L.path ≠ 0 := by (clear * - hp1; omega)
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane p i + 13 ≤ hashedLen p / 8 := by simp only at hin_; (clear * - hin_; omega)
      refine LE _ _ (by (clear * - hT hl hEL h13; omega)) (by (clear * - hcapb hl hpl; omega)) ?_
      rw [show lay.sb + (eLane p i + 9 + l) = lay.sb + eLane p o.i0 + posStride o.L * jj + slotOff o.L o.L.path + 9 + l
          by (clear * - hEL; omega),
        show lay.sb + (eLane p o.ce + 1 + o.co / 8 + 4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path)
          (o.L.height - o.L.path) + l) = lay.sb + (eLane p o.ce + 1 + o.co / 8) +
          4 * posL p ws (o.pe + jj / 8) (jj % 8 * o.L.height + o.L.path) (o.L.height - o.L.path) + l by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      exact e
  -- the constant lanes
  have m0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  have m1 : (lay.sb + 1, lay.sb + 2, lane1C) ∈ qltEntries p lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  refine ⟨⟨by (clear * - hws hT hL8; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m0
    exact LV 0 _ (by (clear * - b3; omega)) b5 (by simpa using (QE _ _ _ m0).1)
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m1
    exact LV 1 _ (by (clear * - b3; omega)) b5 (QE _ _ _ m1).1
  · intro i h1 hi
    cases hk : ((plan p).getD i default).k with
    | q0 =>
      have := streamOk_entry hS.1 hi
      simp only [entryOk, hk] at this
      simp at this; (clear * - h1 this; omega)
    | fs st =>
      have hm := FSM i hi st hk
      obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
      exact LV _ _ (by (clear * - b3; omega)) b5 (QE _ _ _ hm).1
    | leaf =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
    | node pe h j lvl cap =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
  · intro i hi st hk l hl
    have hm := FSM i hi st hk
    obtain ⟨-, -, b3, b4, -⟩ := QB _ _ _ hm
    have e := (QE _ _ _ hm).2 l hl
    refine LE _ _ (by (clear * - hl b3; omega)) (by (clear * - hl b4; omega)) ?_
    rw [show lay.sb + (eLane p i + 1 + l) = lay.sb + eLane p i + 1 + l by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
      show lay.sb + (ansLane p st + l) = lay.sb + ansLane p st + l by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
    exact e
  · intro i hi pe h j lvl cap hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, hnode, -⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hk
      exact hnode hy0 l hl
  · intro i hi pe h j lvl ce co path hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, -, hcap⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, hc⟩ := hk
      by_cases hyp : y = o.L.path
      · rw [if_pos hyp] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hcap hyp l hl
      · rw [if_neg hyp] at hc; cases hc
  · -- the padding
    intro q hq1 hq2
    have hk : q / 8 - hashedLen p / 8 < 17 * nBlk (hashedLen p) - hashedLen p / 8 := by (clear * - hL8 hq1 hq2; omega)
    have hm : (lay.sb + q / 8, lay.sb + q / 8 + 1, padLane (hashedLen p) (q / 8)) ∈ qltEntries p lay := by
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨q / 8 - hashedLen p / 8, List.mem_range.mpr hk, by
        simp only [show hashedLen p / 8 + (q / 8 - hashedLen p / 8) = q / 8 by (clear * - hL8 hq1; omega)]⟩
    obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
    have hv := LV _ _ (by (clear * - b3; omega)) b5 (QE _ _ _ hm).1
    have hb := byte_of_lane ws (q / 8) (q % 8) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega)))
    rw [show 8 * (q / 8) + q % 8 = q by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega)), hv, padLane_byte _ _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega))),
      show 8 * (q / 8) + q % 8 = q by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega))] at hb
    exact hb

/-- **Q_link is sound**: its rows and assertions, with its inputs where the layout says, make the
stream meet every lane condition of the schedule, and pin the trace sponge's padding. -/
theorem qlink_sound (hS : StreamOk p) (hQ : QOk p lay) (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink p lay pt).2) (hA : SegsAssert M pt (qlink p lay pt).2) :
    LaneLink p ws ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  simp only [qlink] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  exact qlinkCore_sound hS hQ hin hws hinj hN hNs h.2 hA.2

/-! ## The position cells (A20) -/

theorem posLoop_spec {pt : Ptr} {a lo hi : Nat} (h : SegsHold c M pt (posLoop a lo hi pt).2) :
    ∀ g < 2 ^ a, M.k (pt.k + g) = M.k (lo + g) + M.k (hi + g) := by
  intro g hg
  have e := lrel_lin (t := 0) rfl (loop_rel h (jf := g) (by simpa using hg) (by simp))
  simp only [List.getD_cons_zero, List.getD_cons_succ, ofK_one, one_mul, ofK_zero, add_zero,
    Opd.val_absK, LoopOut.cell_val] at e
  simp only [loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, List.getD_cons_zero, List.take_zero,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Ptr.at, unflat_one' (show g < 2 ^ [a].sum by simpa using hg),
    Loop.dot] at e
  rw [← ofK_add] at e
  simpa [Mem.rd] using ofK_inj e

theorem sum_take_add_lt (l : List Nat) {k : Nat} (hk : k < l.length) : (l.take k).sum + l[k] ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop k l, List.sum_append, List.drop_eq_getElem_cons hk, List.sum_cons]
  (clear * - k l hk; omega)

theorem posIdx_lt (hQ : QOk p lay) {k j : Nat} (hk : k < (opens p).length)
    (hj : j < ((opens p).getD k default).L.t) : posIdx p k j < 2 ^ lay.pa := by
  have := sum_take_add_lt ((opens p).map fun o => o.L.t) (k := k) (by simpa using hk)
  rw [← List.map_take] at this
  simp only [List.getElem_map] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
  have := hQ.pos
  simp only [posIdx]; omega

/-- **The position cells** (A20): where Q_link's rows hold, the cell `pt.k + posIdx p k j` (position `j`
of opening `k`) is the sum of the position's two BITS fields. -/
theorem qlink_pos (hQ : QOk p lay) {pt : Ptr} (h : SegsHold c M pt (qlink p lay pt).2) {k j : Nat}
    (hk : k < (opens p).length) (hj : j < ((opens p).getD k default).L.t) :
    M.k (pt.k + posIdx p k j) = M.k (lay.fl + posIdx p k j) + M.k (lay.fl + 2 ^ lay.pa + posIdx p k j) := by
  simp only [qlink] at h
  rw [hold_bind] at h
  exact posLoop_spec h.1 _ (posIdx_lt hQ hk hj)

end

end Lvm.QLink
