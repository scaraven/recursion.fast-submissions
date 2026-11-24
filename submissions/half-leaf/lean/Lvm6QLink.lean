-- New for lvm6 (WP CA, Q_link). Season 1's `Q_link` program and its soundness (`LvmQLinkSound`:
-- `qlink`, `open_facts`, `qlinkCore_sound`) re-targeted from a schedule's `plan p`/`opens p` to an lvm6
-- plan `P : List PE6` and its openings `os` (checked against `P` by `opensOK`); the seed's statement
-- lanes checked against cells; its gadgets (`qltLoop`, `capLoop`, `nodeLoop`, `stepArr`) reused unchanged.
import Lvm6QLinkBridge

/-!
# `Q_link` for lvm6 (CA-2)

* **`Open6Q`**: an opening of the plan (first entry, `t` positions of `row`-byte leaves and `path`
  node queries, heights `h`, positions from draw `pd0 + j / per` at bit `(j mod per)·h`, cap at
  `(ce, co)`); **`opensOK P os`**: every opening sits in `P` at its first entry and every leaf or
  node entry of `P` lies in one (decided per `Shape`).
* **`qlink6 P os lay`**: the step array, the QLT loop (constant, length, chain and seed lanes, the
  sponge padding), per opening its cap and node loops (season 1's), and `seedChk` (no rows at FORMAT6
  v2.5: the seed is a chain entry and `Q_sig` binds the statement; v2.2's `seed` class keeps its check).
* **`qlink6_sound`**: where its rows and assertions hold, with its inputs where `Layout6` says
  (`QIn6`) and the static checks (`qOk6`), `QLinkConcl P c ws` for `c` the cells `lay.cp`.
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.QLink Lvm.Loop Lvm.Loop.Build

/-! ## Openings -/

/-- An opening of the plan. -/
structure Open6Q where
  i0 : ℕ
  t : ℕ
  row : ℕ
  path : ℕ
  h : ℕ
  pd0 : ℕ
  per : ℕ
  ce : ℕ
  co : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The entries of an opening. -/
def Open6Q.plan (o : Open6Q) : List PE6 :=
  (List.range o.t).flatMap fun j => ⟨.leaf, o.row⟩ :: (List.range o.path).map fun lvl =>
    ⟨.node (o.pd0 + j / o.per) (j % o.per * o.h) o.h lvl
      (if lvl + 1 = o.path then some (o.ce, o.co, o.path) else none), 64⟩

/-- A leaf or a node entry. -/
def EK6.isOpen : EK6 → Bool
  | .leaf => true
  | .node .. => true
  | _ => false

/-- **The openings match the plan** (decided per `Shape`). -/
def opensOK (P : List PE6) (os : List Open6Q) : Bool :=
  (os.all fun o => decide (2 ≤ o.i0) && decide (o.i0 + o.t * (1 + o.path) ≤ P.length) &&
    decide ((P.drop o.i0).take (o.t * (1 + o.path)) = o.plan)) &&
  P.zipIdx.all fun x => !x.1.k.isOpen ||
    os.any fun o => decide (o.i0 ≤ x.2) && decide (x.2 < o.i0 + o.t * (1 + o.path))

/-- The openings of a schedule (mirrors `walk`): one per `open` item with its cap found. -/
def opensGo (lv : ℕ → Lv) : WS6 → List It → List Open6Q
  | _, [] => []
  | w, it :: its =>
    (match it with
     | .open i =>
       let L := lv i
       match w.caps.find? (·.1 == i) with
       | none => []
       | some (_, ce, co, _) =>
         [⟨w.i, L.t, L.leaf, L.path, L.ht, w.i - 1 - L.gap - (L.d - 1), ppa L.ht, ce, co⟩]
     | _ => []) ++ opensGo lv (walkIt lv w it).2 its

/-- **The openings of a schedule's plan.** -/
def opens6 (lv : ℕ → Lv) (its : List It) : List Open6Q := opensGo lv w06 its

theorem Open6Q.plan_length (o : Open6Q) : o.plan.length = o.t * (1 + o.path) := by
  simp [Open6Q.plan, List.length_flatMap]; left; ring

/-- The entry at position `j`, slot `y` (`0` the leaf, `1 + lvl` the nodes) of an opening. -/
theorem Open6Q.plan_getD (o : Open6Q) {j y : ℕ} (hj : j < o.t) (hy : y < 1 + o.path) :
    o.plan.getD (j * (1 + o.path) + y) default =
      if y = 0 then ⟨.leaf, o.row⟩
      else ⟨.node (o.pd0 + j / o.per) (j % o.per * o.h) o.h (y - 1)
        (if y = o.path then some (o.ce, o.co, o.path) else none), 64⟩ := by
  suffices h : ∀ (n k : ℕ) (j : ℕ), j < n →
      ((List.range' k n).flatMap fun j => (⟨.leaf, o.row⟩ : PE6) :: (List.range o.path).map fun lvl =>
        ⟨.node (o.pd0 + j / o.per) (j % o.per * o.h) o.h lvl
          (if lvl + 1 = o.path then some (o.ce, o.co, o.path) else none), 64⟩).getD
          (j * (1 + o.path) + y) default =
      if y = 0 then ⟨.leaf, o.row⟩
      else ⟨.node (o.pd0 + (k + j) / o.per) ((k + j) % o.per * o.h) o.h (y - 1)
        (if y = o.path then some (o.ce, o.co, o.path) else none), 64⟩ by
    simpa [Open6Q.plan, List.range_eq_range'] using h o.t 0 j hj
  intro n
  induction n with
  | zero => intro k j hj; omega
  | succ n ih =>
    intro k j hj
    rw [List.range'_succ, List.flatMap_cons]
    rcases j with _ | j
    · simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rcases y with _ | y
      · simp
      · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [Nat.add_one_inj]
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have := ih (k + 1) j (by omega)
      rw [show k + (j + 1) = k + 1 + j by omega]
      rw [← this]
      congr 1
      simp only [Nat.succ_mul, List.length_cons, List.length_map, List.length_range]
      ring_nf; omega

section
variable {P : List PE6} {os : List Open6Q}

theorem opensOK_mem (h : opensOK P os = true) {o : Open6Q} (ho : o ∈ os) :
    2 ≤ o.i0 ∧ o.i0 + o.t * (1 + o.path) ≤ P.length ∧ (P.drop o.i0).take (o.t * (1 + o.path)) = o.plan := by
  simp only [opensOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨(h.1 o ho).1.1, (h.1 o ho).1.2, (h.1 o ho).2⟩

theorem opensOK_at (h : opensOK P os = true) {o : Open6Q} (ho : o ∈ os) {x : ℕ} (hx : x < o.t * (1 + o.path)) :
    P.getD (o.i0 + x) default = o.plan.getD x default := by
  obtain ⟨-, hlen, he⟩ := opensOK_mem h ho
  rw [← he, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hx,
    List.getElem?_drop]

/-- **An opening entry: its opening, position and slot.** -/
theorem open_pos6 (h : opensOK P os = true) {i : ℕ} (hi : i < P.length)
    (he : (P.getD i default).k.isOpen = true) :
    ∃ k, k < os.length ∧ ∃ o, os.getD k default = o ∧ ∃ jj y, jj < o.t ∧ y < 1 + o.path ∧
      i = o.i0 + jj * (1 + o.path) + y ∧
      P.getD i default = if y = 0 then ⟨.leaf, o.row⟩
        else ⟨.node (o.pd0 + jj / o.per) (jj % o.per * o.h) o.h (y - 1)
          (if y = o.path then some (o.ce, o.co, o.path) else none), 64⟩ := by
  have h2 := h
  simp only [opensOK, Bool.and_eq_true, List.all_eq_true] at h2
  have hx := h2.2 (P[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]))
  have hgi : P.getD i default = P[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hgi] at he
  simp only [he, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨o, ho, h1, h2'⟩ := hx
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  have hP : 0 < 1 + o.path := by omega
  have hxd : (i - o.i0) / (1 + o.path) * (1 + o.path) + (i - o.i0) % (1 + o.path) = i - o.i0 :=
    Nat.div_add_mod' _ _
  have hjt : (i - o.i0) / (1 + o.path) < o.t := by
    rw [Nat.div_lt_iff_lt_mul hP]; omega
  have e := o.plan_getD hjt (Nat.mod_lt (i - o.i0) hP)
  rw [hxd] at e
  refine ⟨k, hk, o, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hko],
    (i - o.i0) / (1 + o.path), (i - o.i0) % (1 + o.path), hjt, Nat.mod_lt _ hP, by omega, ?_⟩
  rw [← e, ← opensOK_at h ho (by omega), show o.i0 + (i - o.i0) = i by omega]

/-- The lane offset of slot `y` from its position's leaf. -/
def slotOff6 (o : Open6Q) (y : ℕ) : ℕ := if y = 0 then 0 else 5 + o.row / 8 + 13 * (y - 1)

/-- The lanes of one position of an opening. -/
def posStride6 (o : Open6Q) : ℕ := 5 + o.row / 8 + 13 * o.path

/-- **The lanes inside an opening are affine.** -/
theorem eLane_open6 (hS : streamOkL6 P = true) (hO : opensOK P os = true) {o : Open6Q} (ho : o ∈ os) {j y : ℕ}
    (hj : j < o.t) (hy : y ≤ o.path) :
    eLane6 P (o.i0 + j * (1 + o.path) + y) = eLane6 P o.i0 + j * posStride6 o + slotOff6 o y := by
  obtain ⟨h2, hlen, -⟩ := opensOK_mem hO ho
  have entry : ∀ j' < o.t, ∀ y' < 1 + o.path, (P.getD (o.i0 + j' * (1 + o.path) + y') default).len =
      if y' = 0 then o.row else 64 := by
    intro j' hj' y' hy'
    rw [Nat.add_assoc, opensOK_at hO ho (by nlinarith), o.plan_getD hj' hy']
    split <;> rfl
  have hrow8 : o.row % 8 = 0 := by
    have := streamOk6_len hS (i := o.i0) (by omega) (by nlinarith)
    have e := entry 0 (by omega) 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, ite_true] at e
    rw [e] at this; exact this
  have within : ∀ j' < o.t, ∀ y' ≤ o.path, eLane6 P (o.i0 + j' * (1 + o.path) + y') =
      eLane6 P (o.i0 + j' * (1 + o.path)) + slotOff6 o y' := by
    intro j' hj' y'
    induction y' with
    | zero => intro _; simp [slotOff6]
    | succ y' ih =>
      intro hy'
      have hlt : o.i0 + j' * (1 + o.path) + y' < P.length := by
        have : (j' + 1) * (1 + o.path) ≤ o.t * (1 + o.path) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this; omega
      rw [← Nat.add_assoc, eLane6_succ hS (by omega) hlt, ih (by omega), entry j' hj' y' (by omega)]
      simp only [slotOff6, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      split
      · next h => subst h; simp; omega
      · next h => omega
  have leaf : ∀ j' < o.t, eLane6 P (o.i0 + j' * (1 + o.path)) = eLane6 P o.i0 + j' * posStride6 o := by
    intro j'
    induction j' with
    | zero => intro _; simp
    | succ j' ih =>
      intro hj'
      have hstep : o.i0 + (j' + 1) * (1 + o.path) = o.i0 + j' * (1 + o.path) + o.path + 1 := by ring
      have hlt : o.i0 + j' * (1 + o.path) + o.path < P.length := by
        have : (j' + 1) * (1 + o.path) ≤ o.t * (1 + o.path) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this; omega
      rw [hstep, eLane6_succ hS (by omega) hlt, within j' (by omega) o.path le_rfl,
        ih (by omega), entry j' (by omega) o.path (by omega)]
      simp only [slotOff6, posStride6]
      split
      · next h => rw [h]; ring_nf
      · next h =>
        have : 13 * o.path = 13 * (o.path - 1) + 13 := by omega
        rw [Nat.add_mul, this]; ring_nf
  rw [within j hj y hy, leaf j hj]

end

/-! ## Layout, inputs, static checks -/

/-- Where `Q_link`'s cells are. -/
structure Layout6 where
  /-- Stream word `j` is the `K` cell `sb + j`. -/
  sb : ℕ
  /-- The node flag cell. -/
  fg : ℕ
  /-- The QLT table: entry `k` at cells `qt + 3k + {0, 1, 2}`. -/
  qt : ℕ
  /-- The position bits: per opening, `h` cells per (padded) position. -/
  bb : ℕ
  /-- `readd` region: the stream cells `[sb, sb + 2^m)`. -/
  m : ℕ
  /-- The step array has `2^K` flags then `2^K` zeros. -/
  K : ℕ
  /-- The QLT loop has `2^aQ` iterations. -/
  aQ : ℕ
  /-- The child's statement `c'` (4 cells). -/
  cp : ℕ
  deriving Repr, Inhabited

/-- The bit region of opening `k` (the openings before it, padded). -/
def bitBase6 (os : List Open6Q) (lay : Layout6) (k : ℕ) : ℕ :=
  lay.bb + ((os.take k).map fun o => padT o.t * o.h).sum

/-- The QLT entries `(e₁, e₂, v)`: words 0, 1; every chain entry and the seed; the padding words. -/
def qltEntries6 (P : List PE6) (lay : Layout6) : List (ℕ × ℕ × ℕ) :=
  [(lay.sb, lay.sb + 1, lane0C), (lay.sb + 1, lay.sb + 2, lane1C6)] ++
  (P.zipIdx.filterMap fun x => match x.1.k with
    | .fs st _ => some (lay.sb + eLane6 P x.2, lay.sb + ansLane6 P st, x.1.len)
    | .seed => some (lay.sb + eLane6 P x.2, lay.sb + ansLane6 P 0, x.1.len)
    | _ => none) ++
  ((List.range (17 * nBlk (hashedLen6 P) - hashedLen6 P / 8)).map fun k =>
    let q := hashedLen6 P / 8 + k
    (lay.sb + q, lay.sb + q + 1, padLane (hashedLen6 P) q))

/-- The QLT entries padded to `2^aQ` with copies of the first. -/
def qltPadded6 (P : List PE6) (lay : Layout6) : List (ℕ × ℕ × ℕ) :=
  qltEntries6 P lay ++ List.replicate (2 ^ lay.aQ - (qltEntries6 P lay).length) (lay.sb, lay.sb + 1, lane0C)

/-- **The QLT input cells**: per entry `g^e₁, g^e₂, v`. -/
def qltData6 (P : List PE6) (lay : Layout6) : List FK := tblOf (qltPadded6 P lay)

/-- **Where `Q_link`'s inputs are**, and the flag. -/
structure QIn6 (P : List PE6) (os : List Open6Q) (lay : Layout6) (ws : List Word) (M : Mem) : Prop where
  flag : M.k lay.fg = 1
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK ws j
  table : ∀ x < (qltData6 P lay).length, M.k (lay.qt + x) = (qltData6 P lay).getD x 0
  /-- The position bits (BITS): bit `z` of position `j` of opening `k`. -/
  bits : ∀ k < os.length, ∀ j < (os.getD k default).t, ∀ z < (os.getD k default).h,
    M.k (bitBase6 os lay k + (os.getD k default).h * j + z) =
      if ansBit6 P ws ((os.getD k default).pd0 + j / (os.getD k default).per)
        (j % (os.getD k default).per * (os.getD k default).h + z) then 1 else 0

/-- **`Q_link`'s static conditions.** -/
structure QOk6 (P : List PE6) (os : List Open6Q) (lay : Layout6) : Prop where
  qlen : (qltEntries6 P lay).length ≤ 2 ^ lay.aQ
  qbound : ∀ e ∈ qltEntries6 P lay, lay.sb ≤ e.1 ∧ lay.sb ≤ e.2.1 ∧ e.1 + 5 ≤ lay.sb + 2 ^ lay.m ∧
    e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m ∧ e.2.2 < 2 ^ 64
  hT : hashedLen6 P / 8 + 17 ≤ 2 ^ lay.m
  opens : ∀ o ∈ os, 1 ≤ o.path ∧ o.path < o.h ∧ (∀ c ∈ pchunks o.t, c.2 ≤ lay.K) ∧
    eLane6 P o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.h - o.path) ≤ 2 ^ lay.m ∧ o.row < 2 ^ 64

/-- **`Q_link`'s static conditions as one Boolean** (decided per `Shape` and layout). -/
def qOk6 (P : List PE6) (os : List Open6Q) (lay : Layout6) : Bool :=
  decide ((qltEntries6 P lay).length ≤ 2 ^ lay.aQ) &&
    (qltEntries6 P lay).all (fun e => decide (lay.sb ≤ e.1) && decide (lay.sb ≤ e.2.1) &&
      decide (e.1 + 5 ≤ lay.sb + 2 ^ lay.m) && decide (e.2.1 + 4 ≤ lay.sb + 2 ^ lay.m) && decide (e.2.2 < 2 ^ 64)) &&
    decide (hashedLen6 P / 8 + 17 ≤ 2 ^ lay.m) &&
    os.all (fun o => decide (1 ≤ o.path) && decide (o.path < o.h) && (pchunks o.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (eLane6 P o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.h - o.path) ≤ 2 ^ lay.m) && decide (o.row < 2 ^ 64))

theorem qOk6_sound {P : List PE6} {os : List Open6Q} {lay : Layout6} (h : qOk6 P os lay = true) : QOk6 P os lay := by
  simp only [qOk6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun e he => by obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩ := h2 e he; exact ⟨a, b, c, d, f⟩, h3,
    fun o ho => by obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩ := h4 o ho; exact ⟨a, b, c, d, f⟩⟩

/-! ## The program -/

/-- The loops of one opening (`zo` the step array, `bo` the opening's bit region). -/
def openLoops6 (P : List PE6) (lay : Layout6) (zo bo : ℕ) (o : Open6Q) : BM Unit := do
  let ℓO := eLane6 P o.i0
  let Sj := posStride6 o
  let capL := eLane6 P o.ce + 1 + o.co / 8
  let _ ← seqAll ((pchunks o.t).map fun c => do
    let gz := zo + 2 ^ lay.K - realCount o.t c.1 c.2
    capLoop [c.2] (lay.sb + ℓO + Sj * c.1) o.row (lay.sb + ℓO + Sj * c.1 + slotOff6 o o.path + 9)
      (lay.sb + capL) lay.sb lay.m [Sj] (bo + o.h * c.1 + o.path) [o.h] (o.h - o.path) gz [1]
    let _ ← seqAll ((chunks o.path).map fun d =>
      nodeLoop [d.2, c.2] (lay.sb + ℓO + Sj * c.1 + slotOff6 o (d.1 + 1))
        (lay.sb + ℓO + Sj * c.1 + slotOff6 o (d.1 + 1) + 1) (lay.sb + ℓO + Sj * c.1 + slotOff6 o (d.1 + 1) + 5)
        (lay.sb + ℓO + Sj * c.1 + slotOff6 o (d.1 + 1) - 4) [13, Sj]
        (bo + o.h * c.1 + d.1) [1, o.h] gz [0, 1])
    pure ())
  pure ()

/-- **The seed check.** FORMAT6 v2.5's seed `a₀ ‖ HDR` is a chain entry (`fs 0 0`, CA2's `planOf`): its
`a₀` lanes are checked by the QLT loop like every chain query's state, and it carries no statement words, so
there are no rows here. The child's statement `c` is bound by `Q_sig`: `hdrCopy6` copies the seed's `HDR`
words (stream words `hdrW k = eLane6 P 1 + 5 + k`, `seedLane_hdrW`) to season 1's header cells, and
`ChildOkS` checks `c = stmtOf HDR` against the cells `I.cL`; with `I.cL = lay.cp`, `childLink6` gives
`QLinkConcl` and `ChildHdr6` for the same `c`. A plan whose entry 1 is of v2.2's `seed` class
(`a₀ ‖ c ‖ HDR`, `plan6`) keeps v2.2's check: seed words 5–8 (`c`) against the cells `lay.cp`. -/
def seedChk (P : List PE6) (lay : Layout6) : BM Unit :=
  if (P.getD 1 default).k = .seed then do
    let _ ← forN 4 fun l => assertEq (kc (lay.sb + eLane6 P 1 + 5 + l)) (kc (lay.cp + l)) (kc lay.fg)
    pure ()
  else pure ()

/-- **`Q_link`** for an lvm6 plan and its openings. -/
def qlink6 (P : List PE6) (os : List Open6Q) (lay : Layout6) : BM Unit := do
  let zo ← stepArr lay.K (kc lay.fg)
  qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)
  let _ ← seqAll ((List.range os.length).map fun k => openLoops6 P lay zo (bitBase6 os lay k) (os.getD k default))
  seedChk P lay

/-! ## Soundness -/

theorem qltPadded6_length (P : List PE6) (lay : Layout6) (h : (qltEntries6 P lay).length ≤ 2 ^ lay.aQ) :
    (qltPadded6 P lay).length = 2 ^ lay.aQ := by
  simp [qltPadded6]; omega

section
variable {P : List PE6} {os : List Open6Q} {lay : Layout6} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Every QLT entry's checks hold.** -/
theorem qlt_entry6 (hQ : QOk6 P os lay) (hin : QIn6 P os lay ws M) {N : ℕ} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    (hA : SegsAssert M pt (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg) pt).2)
    {e : ℕ × ℕ × ℕ} (he : e ∈ qltEntries6 P lay) :
    M.k e.1 = kOf e.2.2 ∧ ∀ l < 4, M.k (e.1 + 1 + l) = M.k (e.2.1 + l) := by
  have hmem : e ∈ qltPadded6 P lay := List.mem_append_left _ he
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hmem
  rw [qltPadded6_length P lay hQ.qlen] at hk
  have hkd : (qltPadded6 P lay).getD k (0, 0, 0) = e := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [qltPadded6_length P lay hQ.qlen]; exact hk)]
    simpa using hke
  have hd := tblOf_getD (qltPadded6 P lay) (k := k) (by rw [qltPadded6_length P lay hQ.qlen]; exact hk)
  rw [hkd] at hd
  have hlenD : (qltData6 P lay).length = 3 * 2 ^ lay.aQ := by
    rw [qltData6, tblOf_length, qltPadded6_length P lay hQ.qlen]
  have t0 := hin.table (3 * k) (by omega)
  have t1 := hin.table (3 * k + 1) (by omega)
  have t2 := hin.table (3 * k + 2) (by omega)
  simp only [qltData6] at t0 t1 t2
  rw [hd.1] at t0; rw [hd.2.1] at t1; rw [hd.2.2] at t2
  obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound e he
  have := qltLoop_spec h hA hin.flag hinj hN (jf := k) (e₁ := e.1) (e₂ := e.2.1) hk (by omega) (by omega)
    t0 (by rw [show lay.qt + 1 + 3 * k = lay.qt + (3 * k + 1) by ring]; exact t1)
  rw [show lay.qt + 2 + 3 * k = lay.qt + (3 * k + 2) by ring, t2] at this
  exact this

end

theorem bitSum_posL6 {P : List PE6} {ws : List Word} {M : Mem} {bt e s n : ℕ}
    (hb : ∀ y < n, M.k (bt + y) = if ansBit6 P ws e (s + y) then 1 else 0) :
    bitSum M bt [] [] n = posL6 P ws e s n := by
  simp only [bitSum, posL6]
  congr 1
  apply List.map_congr_left
  intro y hy
  rw [show bt + y + Loop.dot [] [] = bt + y from rfl, hb y (List.mem_range.mp hy)]
  split <;> simp [fk01]

theorem lanes_in6 {P : List PE6} (hS : streamOkL6 P = true) {i : ℕ} (h1 : 1 ≤ i) (hi : i < P.length) :
    eLane6 P i + 5 + (P.getD i default).len / 8 ≤ hashedLen6 P / 8 := by
  have e := entry6_end P hi
  rw [bOff6_eq hS h1 (by omega)] at e
  have := streamOk6_len hS h1 hi
  omega

/-- Four stream words as the digest `digAt` reads from cells holding them. -/
theorem wordsBytes_digAt {ws : List Word} {M : Mem} {a b : ℕ} (hlen : a + 4 ≤ ws.length)
    (h : ∀ l < 4, M.k (b + l) = laneK ws (a + l)) :
    wordsBytes ((ws.drop a).take 4) = (Lvm.QSig.digAt M.k b).toList := by
  refine List.ext_getElem (by simp [wordsBytes_length]; omega) fun k h1 h2 => ?_
  simp only [List.length_ofFn, Vector.length_toList] at h2
  rw [← List.getD_eq_getElem _ 0 h1, ← wordByte_eq_getD]
  simp only [Lvm.QSig.digAt, Lvm.Wots.digOfW, Vector.toList_ofFn, List.getElem_ofFn]
  rw [Lvm.Wots.byteW_toNat _ (by omega), h (k / 8) (by omega), wordByte, lw_of_slice (by omega) hlen]
  rfl


section
variable {P : List PE6} {os : List Open6Q} {lay : Layout6} {ws : List Word} {c : Ctx} {M : Mem}

/-- **An opening's checks hold at every position.** -/
theorem open_facts6 (hQ : QOk6 P os lay) (hin : QIn6 P os lay ws M) {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N)
    (hNs : lay.sb + 2 ^ lay.m ≤ N) {zo : Nat} (hz : ∀ x < 2 ^ lay.K, M.k (zo + x) = 1)
    {k : Nat} (hk : k < os.length) {o : Open6Q} (hko : os.getD k default = o) {q : Ptr}
    (h : SegsHold c M q (openLoops6 P lay zo (bitBase6 os lay k) o q).2)
    (hA : SegsAssert M q (openLoops6 P lay zo (bitBase6 os lay k) o q).2)
    {j : Nat} (hj : j < o.t) :
    M.k (lay.sb + eLane6 P o.i0 + posStride6 o * j) = kOf o.row ∧
    (∀ l < 4, M.k ((lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o o.path + 9 + l) =
      M.k (lay.sb + (eLane6 P o.ce + 1 + o.co / 8) +
        4 * bitSum M (bitBase6 os lay k + o.h * j + o.path) [] [] (o.h - o.path) + l)) ∧
    (∀ lvl < o.path, M.k ((lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1)) = kOf 64 ∧ ∀ l < 4,
      M.k ((lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) - 4 + l) =
        if M.k (bitBase6 os lay k + o.h * j + lvl) = 1 then M.k ((lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) + 5 + l)
        else M.k ((lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) + 1 + l)) := by
  have ho : o ∈ os := by
    rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1, hph, hK, hcap, hrow⟩ := hQ.opens o ho
  have hbit : ∀ j' < o.t, ∀ z < o.h, M.k (bitBase6 os lay k + o.h * j' + z) = 0 ∨
      M.k (bitBase6 os lay k + o.h * j' + z) = 1 := by
    intro j' hj' z hz'
    have := hin.bits k hk j' (by rw [hko]; exact hj') z (by rw [hko]; exact hz')
    rw [hko] at this
    rw [this]; split <;> simp
  simp only [openLoops6] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨cc, hcc, hc1, hc2, hc3⟩ := pchunks_cover hj
  obtain ⟨q1, h1, hA1⟩ := seqAll_both _ _ h.1 hA.1 _ (List.mem_map_of_mem hcc)
  rw [hold_bind] at h1; rw [assert_bind] at hA1
  have hgate : ∀ jj, jj < realCount o.t cc.1 cc.2 →
      M.k (zo + 2 ^ lay.K - realCount o.t cc.1 cc.2 + jj) = 1 := by
    intro jj hjj
    have hr := realCount_le o.t cc.1 cc.2
    have hKc : 2 ^ cc.2 ≤ 2 ^ lay.K := Nat.pow_le_pow_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (hK cc hcc)
    rw [show zo + 2 ^ lay.K - realCount o.t cc.1 cc.2 + jj = zo + (2 ^ lay.K - realCount o.t cc.1 cc.2 + jj) by (clear * - hr hKc; omega)]
    exact hz _ (by (clear * - hjj hr hKc; omega))
  have hjs : j = cc.1 + (j - cc.1) := by (clear * - hc1; omega)
  have hHj : o.h * j = o.h * cc.1 + o.h * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  have hSj : posStride6 o * j = posStride6 o * cc.1 + posStride6 o * (j - cc.1) := by
    rw [← Nat.mul_add, ← hjs]
  -- the cap loop
  have hc' := capLoop_spec h1.1 hA1.1 (jf := j - cc.1) (by simpa using hc3) (by (clear * - hph; omega))
    (by simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero, Nat.one_mul]
        exact hgate _ hc2)
    (fun y hy => by
      simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero]
      have := hbit j hj (o.path + y) (by (clear * - hph hy; omega))
      rwa [show bitBase6 os lay k + o.h * cc.1 + o.path + y + o.h * (j - cc.1) =
        bitBase6 os lay k + o.h * j + (o.path + y) by (clear * - hHj; omega)])
    hinj hN (by (clear * - hNs hcap; omega))
  simp only [unflat_one' (show j - cc.1 < 2 ^ [cc.2].sum by simpa using hc3), Loop.dot, Nat.add_zero] at hc'
  have hbase : lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + posStride6 o * (j - cc.1) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) := by
    (clear * - hSj; omega)
  refine ⟨?_, fun l hl => ?_, fun lvl hlvl => ?_⟩
  · rw [← hbase]; exact hc'.1
  · have := hc'.2 l hl
    rw [show lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o o.path + 9 + l +
        posStride6 o * (j - cc.1) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o o.path + 9 + l by (clear * - hSj; omega)] at this
    rw [this, bitSum_congr M _ (bitBase6 os lay k + o.h * j + o.path) [o.h] [] [j - cc.1] []
      (o.h - o.path) (fun y _ => by simp only [Loop.dot]; (clear * - hHj; omega))]
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
          rwa [show bitBase6 os lay k + o.h * cc.1 + dd.1 + (lvl - dd.1 + o.h * (j - cc.1)) =
            bitBase6 os lay k + o.h * j + lvl by (clear * - hHj hd1; omega)])
    rw [hu] at hn
    simp only [Loop.dot, Nat.add_zero] at hn
    have hsl : slotOff6 o (dd.1 + 1) + 13 * (lvl - dd.1) = slotOff6 o (lvl + 1) := by
      simp only [slotOff6, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]; (clear * - hd1; omega)
    have hb2 : lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o (dd.1 + 1) +
        (13 * (lvl - dd.1) + posStride6 o * (j - cc.1)) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) := by
      (clear * - hSj hsl; omega)
    have hbit' : bitBase6 os lay k + o.h * cc.1 + dd.1 + (1 * (lvl - dd.1) + o.h * (j - cc.1)) =
        bitBase6 os lay k + o.h * j + lvl := by (clear * - hHj hd1; omega)
    refine ⟨by rw [← hb2]; exact hn.1, fun l hl => ?_⟩
    have := hn.2 l hl
    have e1 : lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o (dd.1 + 1) - 4 + l +
        (13 * (lvl - dd.1) + posStride6 o * (j - cc.1)) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) - 4 + l := by
      have : 4 ≤ lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o (dd.1 + 1) := by
        simp only [slotOff6, Nat.add_one_ne_zero, ite_false]; (clear * - hrow; omega)
      (clear * - hSj hsl this; omega)
    have e2 : lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o (dd.1 + 1) + 5 + l +
        (13 * (lvl - dd.1) + posStride6 o * (j - cc.1)) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) + 5 + l := by (clear * - hSj hsl; omega)
    have e3 : lay.sb + eLane6 P o.i0 + posStride6 o * cc.1 + slotOff6 o (dd.1 + 1) + 1 + l +
        (13 * (lvl - dd.1) + posStride6 o * (j - cc.1)) = (lay.sb + eLane6 P o.i0 + posStride6 o * j) + slotOff6 o (lvl + 1) + 1 + l := by (clear * - hSj hsl; omega)
    simp only [hbit', e1, e2, e3] at this
    exact this

end

section
variable {P : List PE6} {os : List Open6Q} {lay : Layout6} {ws : List Word} {c : Ctx} {M : Mem}

/-- **`Q_link`'s lane conditions and the padding**, from its rows. -/
theorem qlink6_lanes (hS : streamOkL6 P = true) (hP2 : 2 ≤ P.length) (hO : opensOK P os = true)
    (hQ : QOk6 P os lay) (hin : QIn6 P os lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink6 P os lay pt).2) (hA : SegsAssert M pt (qlink6 P os lay pt).2) :
    LaneLink6 P (Lvm.QSig.digAt M.k lay.cp) ws ∧ PadOkB (wordsBytes ws) (hashedLen6 P) := by
  simp only [qlink6] at h hA
  rw [hold_bind] at h; rw [assert_bind] at hA
  obtain ⟨hz1, -⟩ := stepArr_spec h.1
  have hz : ∀ x < 2 ^ lay.K, M.k (pt.k + x) = 1 := fun x hx => by rw [hz1 x hx, hin.flag]
  have h2 := h.2; have hA2 := hA.2
  rw [stepArr_apply] at h2 hA2
  rw [hold_bind] at h2; rw [assert_bind] at hA2
  have QE : ∀ a b v, (a, b, v) ∈ qltEntries6 P lay → M.k a = kOf v ∧ ∀ l < 4, M.k (a + 1 + l) = M.k (b + l) :=
    fun a b v he => qlt_entry6 hQ hin hinj hN hNs h2.1 hA2.1 he
  have QB : ∀ a b v, (a, b, v) ∈ qltEntries6 P lay → lay.sb ≤ a ∧ lay.sb ≤ b ∧ a + 5 ≤ lay.sb + 2 ^ lay.m ∧
      b + 4 ≤ lay.sb + 2 ^ lay.m ∧ v < 2 ^ 64 := fun a b v he => hQ.qbound _ he
  have h3 := h2.2; have hA3 := hA2.2
  rw [hold_bind] at h3; rw [assert_bind] at hA3
  have h4 := h3.2; have hA4 := hA3.2
  have hopk : ∀ k, k < os.length → ∀ o, os.getD k default = o →
      ∃ q, SegsHold c M q (openLoops6 P lay pt.k (bitBase6 os lay k) o q).2 ∧
        SegsAssert M q (openLoops6 P lay pt.k (bitBase6 os lay k) o q).2 := by
    intro k hk o hko
    obtain ⟨q, hq1, hq2⟩ := seqAll_both _ _ h3.1 hA3.1 _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    subst hko
    exact ⟨q, hq1, hq2⟩
  -- stream lanes
  have hT := hQ.hT
  have hL8 : hashedLen6 P % 8 = 0 := hashedLen6_mod hS (by omega)
  have LE : ∀ a b, a < 2 ^ lay.m → b < 2 ^ lay.m → M.k (lay.sb + a) = M.k (lay.sb + b) → lw ws a = lw ws b :=
    fun a b ha hb e => lw_of_laneK (by rw [← hin.stream a ha, ← hin.stream b hb, e])
  have LV : ∀ a v, a < 2 ^ lay.m → v < 2 ^ 64 → M.k (lay.sb + a) = kOf v → lw ws a = v :=
    fun a v ha hv e => lw_of_kOf hv (by rw [← hin.stream a ha, e])
  -- FS entries are QLT entries
  have FSM : ∀ i, i < P.length → ∀ st g, (P.getD i default).k = .fs st g →
      (lay.sb + eLane6 P i, lay.sb + ansLane6 P st, (P.getD i default).len) ∈ qltEntries6 P lay := by
    intro i hi st g hk
    have hgi : P.getD i default = P[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [hgi] at hk ⊢
    apply List.mem_append_left; apply List.mem_append_right
    rw [List.mem_filterMap]
    exact ⟨(P[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]),
      by simp only [hk]⟩
  have SDM : ∀ i, i < P.length → (P.getD i default).k = .seed →
      (lay.sb + eLane6 P i, lay.sb + ansLane6 P 0, (P.getD i default).len) ∈ qltEntries6 P lay := by
    intro i hi hk
    have hgi : P.getD i default = P[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [hgi] at hk ⊢
    apply List.mem_append_left; apply List.mem_append_right
    rw [List.mem_filterMap]
    exact ⟨(P[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]),
      by simp only [hk]⟩
  -- opening entries
  have OE : ∀ i, i < P.length → (P.getD i default).k.isOpen = true →
      ∃ k o jj y, k < os.length ∧ os.getD k default = o ∧ jj < o.t ∧ y < 1 + o.path ∧
        P.getD i default = (if y = 0 then ⟨.leaf, o.row⟩ else ⟨.node (o.pd0 + jj / o.per) (jj % o.per * o.h) o.h (y - 1)
          (if y = o.path then some (o.ce, o.co, o.path) else none), 64⟩) ∧
        lw ws (eLane6 P i) = (P.getD i default).len ∧
        (y ≠ 0 → ∀ l < 4, lw ws ((if ansBit6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + (y - 1))
          then eLane6 P i + 5 else eLane6 P i + 1) + l) = lw ws (eLane6 P i - 4 + l)) ∧
        (y = o.path → ∀ l < 4, lw ws (eLane6 P i + 9 + l) = lw ws (eLane6 P o.ce + 1 + o.co / 8 +
          4 * posL6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + o.path) (o.h - o.path) + l)) := by
    intro i hi he
    obtain ⟨k, hk, o, hko, jj, y, hjj, hy, hieq, hpe⟩ := open_pos6 hO hi he
    have ho : o ∈ os := by
      rw [← hko, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
    obtain ⟨q, hq1, hq2⟩ := hopk k hk o hko
    obtain ⟨f1, f2, f3⟩ := open_facts6 hQ hin hinj hN hNs hz hk hko hq1 hq2 hjj
    have hEL : eLane6 P i = eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y := by
      rw [hieq, eLane_open6 hS hO ho hjj (by (clear * - hy; omega)), Nat.mul_comm]
    have hi1 : 1 ≤ i := by have := (opensOK_mem hO ho).1; (clear * - hieq this; omega)
    have hin_ := lanes_in6 hS hi1 hi
    have hbits : ∀ z < o.h, M.k (bitBase6 os lay k + o.h * jj + z) =
        if ansBit6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + z) then 1 else 0 := by
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
        rw [hEL, show lay.sb + (eLane6 P o.i0 + posStride6 o * jj + slotOff6 o 0) =
          lay.sb + eLane6 P o.i0 + posStride6 o * jj by simp [slotOff6]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        exact f1
      · rw [hpe, if_neg hy0]
        rw [hpe, if_neg hy0] at hin_
        have := (f3 (y - 1) (by (clear * - hy hp1; omega))).1
        rw [show y - 1 + 1 = y by (clear * - hy0; omega)] at this
        refine LV _ _ (by (clear * - hT hEL hin_; omega)) (by norm_num) ?_
        rw [hEL, show lay.sb + (eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y) =
          lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
        exact this
    · intro hy0 l hl
      have e := (f3 (y - 1) (by (clear * - hy hp1; omega))).2 l hl
      rw [show y - 1 + 1 = y by (clear * - hy0; omega)] at e
      have hs5 : 5 ≤ slotOff6 o y := by simp only [slotOff6, if_neg hy0]; (clear * - hrow; omega)
      have hb := hbits (y - 1) (by (clear * - hy hp1 hph; omega))
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane6 P i + 13 ≤ hashedLen6 P / 8 := by simp only at hin_; (clear * - hin_; omega)
      by_cases hab : ansBit6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + (y - 1)) = true
      · rw [if_pos hab] at hb ⊢; rw [if_pos hb] at e
        refine (LE _ _ (by (clear * - hT hL8 hEL hl h13; omega)) (by (clear * - hT hEL hin_ hl; omega)) ?_).symm
        rw [show lay.sb + (eLane6 P i - 4 + l) = lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y - 4 + l
            by (clear * - hEL hs5; omega),
          show lay.sb + (eLane6 P i + 5 + l) = lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y + 5 + l
            by (clear * - hEL; omega)]
        exact e
      · rw [if_neg hab] at hb ⊢; rw [hb, if_neg fk01] at e
        refine (LE _ _ (by (clear * - hT hL8 hEL hl h13; omega)) (by (clear * - hT hEL hin_ hl; omega)) ?_).symm
        rw [show lay.sb + (eLane6 P i - 4 + l) = lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y - 4 + l
            by (clear * - hEL hs5; omega),
          show lay.sb + (eLane6 P i + 1 + l) = lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o y + 1 + l
            by (clear * - hEL; omega)]
        exact e
    · intro hyp l hl
      subst hyp
      have e := f2 l hl
      have hbs : bitSum M (bitBase6 os lay k + o.h * jj + o.path) [] [] (o.h - o.path) =
          posL6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + o.path) (o.h - o.path) :=
        bitSum_posL6 fun z hz => by
          have := hbits (o.path + z) (by (clear * - hph hz; omega))
          simpa only [Nat.add_assoc] using this
      rw [hbs] at e
      have hpl := posL6_lt P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + o.path) (o.h - o.path)
      have hy0 : o.path ≠ 0 := by (clear * - hp1; omega)
      rw [hpe, if_neg hy0] at hin_
      have h13 : eLane6 P i + 13 ≤ hashedLen6 P / 8 := by simp only at hin_; (clear * - hin_; omega)
      refine LE _ _ (by (clear * - hT hl hEL h13; omega)) (by (clear * - hcapb hl hpl; omega)) ?_
      rw [show lay.sb + (eLane6 P i + 9 + l) = lay.sb + eLane6 P o.i0 + posStride6 o * jj + slotOff6 o o.path + 9 + l
          by (clear * - hEL; omega),
        show lay.sb + (eLane6 P o.ce + 1 + o.co / 8 + 4 * posL6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + o.path)
          (o.h - o.path) + l) = lay.sb + (eLane6 P o.ce + 1 + o.co / 8) +
          4 * posL6 P ws (o.pd0 + jj / o.per) (jj % o.per * o.h + o.path) (o.h - o.path) + l by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
      exact e
  -- the constant lanes
  have m0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries6 P lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  have m1 : (lay.sb + 1, lay.sb + 2, lane1C6) ∈ qltEntries6 P lay :=
    List.mem_append_left _ (List.mem_append_left _ (by simp))
  -- the seed's statement words
  have SC : (P.getD 1 default).k = .seed → ∀ l < 4, M.k (lay.sb + eLane6 P 1 + 5 + l) = M.k (lay.cp + l) := by
    intro hk1 l hl
    have hs := h4; have hsA := hA4
    simp only [seedChk, if_pos hk1] at hs hsA
    rw [hold_bind] at hs; rw [assert_bind] at hsA
    obtain ⟨q, hq1, hq2⟩ := seqAll_both _ _ hs.1 hsA.1 _ (List.mem_map_of_mem (List.mem_range.mpr hl))
    exact assertEqKK_spec hq1 hq2 hin.flag
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m0
    exact LV 0 _ (by omega) b5 (by simpa using (QE _ _ _ m0).1)
  · obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ m1
    exact LV 1 _ (by omega) b5 (QE _ _ _ m1).1
  · intro i h1 hi
    cases hk : (P.getD i default).k with
    | q0 =>
      have := streamOk6_entry hS hi
      simp only [entryOk6, hk] at this
      simp at this; omega
    | seed =>
      have hm := SDM i hi hk
      obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
      exact LV _ _ (by omega) b5 (QE _ _ _ hm).1
    | fs st g =>
      have hm := FSM i hi st g hk
      obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
      exact LV _ _ (by omega) b5 (QE _ _ _ hm).1
    | leaf =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
    | node pe h j lvl cap =>
      obtain ⟨-, -, -, -, -, -, -, -, -, he, -⟩ := OE i hi (by rw [hk]; rfl); exact he
  · intro i hi st g hk l hl
    have hm := FSM i hi st g hk
    obtain ⟨-, -, b3, b4, -⟩ := QB _ _ _ hm
    have e := (QE _ _ _ hm).2 l hl
    refine LE _ _ (by omega) (by omega) ?_
    rw [show lay.sb + (eLane6 P i + 1 + l) = lay.sb + eLane6 P i + 1 + l by omega,
      show lay.sb + (ansLane6 P st + l) = lay.sb + ansLane6 P st + l by omega]
    exact e
  · intro i hi hk
    have hm := SDM i hi hk
    obtain ⟨-, -, b3, b4, -⟩ := QB _ _ _ hm
    have hE := streamOk6_entry hS hi
    simp only [entryOk6, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨rfl, h64⟩ := hE
    refine ⟨fun l hl => ?_, ?_⟩
    · have e := (QE _ _ _ hm).2 l hl
      refine LE _ _ (by omega) (by omega) ?_
      rw [show lay.sb + (eLane6 P 1 + 1 + l) = lay.sb + eLane6 P 1 + 1 + l by omega,
        show lay.sb + (ansLane6 P 0 + l) = lay.sb + ansLane6 P 0 + l by omega]
      exact e
    · have hin1 := lanes_in6 hS le_rfl hi
      refine wordsBytes_digAt (by omega) fun l hl => ?_
      rw [← SC hk l hl, show lay.sb + eLane6 P 1 + 5 + l = lay.sb + (eLane6 P 1 + 5 + l) by omega]
      exact hin.stream _ (by omega)
  · intro i hi pe sh h lvl cap hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, hnode, -⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK6.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hk
      exact hnode hy0 l hl
  · intro i hi pe sh h lvl ce co path hk l hl
    obtain ⟨k, o, jj, y, -, -, -, -, hpe, -, -, hcap⟩ := OE i hi (by rw [hk]; rfl)
    rw [hpe] at hk
    by_cases hy0 : y = 0
    · rw [if_pos hy0] at hk; cases hk
    · rw [if_neg hy0] at hk
      simp only [EK6.node.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl, hc⟩ := hk
      by_cases hyp : y = o.path
      · rw [if_pos hyp] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hcap hyp l hl
      · rw [if_neg hyp] at hc; cases hc
  · -- the padding
    intro q hq1 hq2
    have hk : q / 8 - hashedLen6 P / 8 < 17 * nBlk (hashedLen6 P) - hashedLen6 P / 8 := by (clear * - hL8 hq1 hq2; omega)
    have hm : (lay.sb + q / 8, lay.sb + q / 8 + 1, padLane (hashedLen6 P) (q / 8)) ∈ qltEntries6 P lay := by
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨q / 8 - hashedLen6 P / 8, List.mem_range.mpr hk, by
        simp only [show hashedLen6 P / 8 + (q / 8 - hashedLen6 P / 8) = q / 8 by (clear * - hL8 hq1; omega)]⟩
    obtain ⟨-, -, b3, -, b5⟩ := QB _ _ _ hm
    have hv := LV _ _ (by (clear * - b3; omega)) b5 (QE _ _ _ hm).1
    have hb := byte_of_lane ws (q / 8) (q % 8) (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega)))
    rw [show 8 * (q / 8) + q % 8 = q by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega)), hv, padLane_byte _ _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega))),
      show 8 * (q / 8) + q % 8 = q by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - q; omega))] at hb
    exact hb

/-- **`Q_link` is sound** (CA-2): its rows and assertions, with its inputs where `Layout6` says and
the static checks, make the stream's trace a trace of the plan for the statement in the cells
`lay.cp`, with the trace sponge's padding in place. -/
theorem qlink6_sound (hS : streamOkL6 P = true) (hP2 : 2 ≤ P.length) (hO : opensOK P os = true)
    (hQ : qOk6 P os lay = true) (hin : QIn6 P os lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink6 P os lay pt).2) (hA : SegsAssert M pt (qlink6 P os lay pt).2) :
    QLinkConcl P (Lvm.QSig.digAt M.k lay.cp) ws := by
  obtain ⟨hL, hpad⟩ := qlink6_lanes hS hP2 hO (qOk6_sound hQ) hin hws hinj hN hNs h hA
  exact ⟨linkOk6_of_laneLink6 hS hL, hpad⟩

end

/-! ## `qOk6` without lane sums (WP CA3) -/

/-- **`Q_link`'s static conditions without the per-entry lane sums** (WP CA3): the bounds of the chain
QLT entries follow from `streamOkL6` and the stream bound (`lanes_in6`), so only their count, the
lengths, the padding entries and the openings are checked. It reads no cell of the layout (`m`, `K`,
`aQ` only), and it is linear in the plan's length (`qOk6`'s direct decision is quadratic). -/
def qOkS6 (P : List PE6) (os : List Open6Q) (m K aQ : ℕ) : Bool :=
  decide ((qltEntries6 P default).length ≤ 2 ^ aQ) &&
    decide (hashedLen6 P / 8 + 17 ≤ 2 ^ m) && decide (17 * nBlk (hashedLen6 P) + 4 ≤ 2 ^ m) &&
    P.all (fun e => decide (e.len < 2 ^ 64)) &&
    (List.range (17 * nBlk (hashedLen6 P) - hashedLen6 P / 8)).all
      (fun k => decide (padLane (hashedLen6 P) (hashedLen6 P / 8 + k) < 2 ^ 64)) &&
    os.all (fun o => decide (1 ≤ o.path) && decide (o.path < o.h) && (pchunks o.t).all (fun c => decide (c.2 ≤ K)) &&
      decide (eLane6 P o.ce + 1 + o.co / 8 + 4 * 2 ^ (o.h - o.path) ≤ 2 ^ m) && decide (o.row < 2 ^ 64))

theorem qltEntries6_length (P : List PE6) (lay lay' : Layout6) :
    (qltEntries6 P lay).length = (qltEntries6 P lay').length := by
  simp only [qltEntries6, List.length_append, List.length_map, List.length_range, List.length_filterMap_eq_countP]
  congr 2
  apply List.countP_congr
  rintro ⟨⟨k, len⟩, i⟩ -
  cases k <;> simp

theorem getD_of_zipIdx {P : List PE6} {x : PE6 × ℕ} (hx : x ∈ P.zipIdx) :
    x.2 < P.length ∧ P.getD x.2 default = x.1 := by
  have h := List.mem_zipIdx_iff_getElem?.mp hx
  have hl : x.2 < P.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨hl, ?_⟩
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

/-- **`qOkS6` gives `qOk6`** at every layout with its `m`, `K`, `aQ`. -/
theorem qOk6_of_S {P : List PE6} {os : List Open6Q} {lay : Layout6} (hS : streamOkL6 P = true)
    (h : qOkS6 P os lay.m lay.K lay.aQ = true) : qOk6 P os lay = true := by
  simp only [qOkS6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hlen, hT⟩, hT2⟩, hL64⟩, hpad⟩, hos⟩ := h
  simp only [qOk6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨by rwa [qltEntries6_length P lay default], fun e he => ?_⟩, hT⟩, hos⟩
  have h6 : 6 ≤ 2 ^ lay.m := by omega
  simp only [qltEntries6, List.mem_append, List.mem_cons, List.mem_filterMap, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl) | ⟨x, hx, hf⟩) | ⟨k, hk, rfl⟩
  · refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> dsimp only <;> first | omega | decide
  · refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> dsimp only <;> first | omega | decide
  · obtain ⟨hi, hg⟩ := getD_of_zipIdx hx
    obtain ⟨⟨k, len⟩, i⟩ := x
    simp only at hi hg
    have hE := streamOk6_entry hS hi
    have hlt := hL64 _ (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hx))
    rw [hg] at hE
    cases k with
    | fs st g =>
      simp only [Option.some.injEq] at hf; subst hf
      simp only [entryOk6, Bool.and_eq_true, decide_eq_true_eq] at hE
      obtain ⟨⟨h32, hst⟩, h1⟩ := hE
      have hin := lanes_in6 hS h1 hi
      have hA : ansLane6 P st + 4 ≤ hashedLen6 P / 8 + 17 := by
        unfold ansLane6
        split
        · omega
        · have := lanes_in6 hS (by omega) (show st < P.length by omega); omega
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp only at hlt ⊢ <;> omega
    | seed =>
      simp only [Option.some.injEq] at hf; subst hf
      simp only [entryOk6, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hE
      obtain ⟨rfl, -⟩ := hE
      have hin := lanes_in6 hS le_rfl hi
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp only [ansLane6, if_pos] at hlt ⊢ <;> omega
    | q0 => simp at hf
    | leaf => simp at hf
    | node => simp at hf
  · have := hpad k hk
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> dsimp only <;> omega

/-- `qOkS6` is monotone in `m`, `K`, `aQ`. -/
theorem qOkS6_mono {P : List PE6} {os : List Open6Q} {m K aQ m' K' aQ' : ℕ} (h : qOkS6 P os m K aQ = true)
    (hm : m ≤ m') (hK : K ≤ K') (haQ : aQ ≤ aQ') : qOkS6 P os m' K' aQ' = true := by
  have pm := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
  have pa := Nat.pow_le_pow_right (show 0 < 2 by norm_num) haQ
  simp only [qOkS6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, h4⟩, h5⟩, fun o ho => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩ := h6 o ho
  exact ⟨⟨⟨⟨a, b⟩, fun x hx => le_trans (c x hx) hK⟩, by omega⟩, f⟩

/-- **`Q_link` is sound, with its lane conditions** (WP CA3, for CB's trace digest `traceDigest6`, which
reads `LaneLink6`): `qlink6_sound`'s conclusion together with `LaneLink6` (not implied by `QLinkConcl`:
the length words and the constant lanes are not in `LinkOk6`), from one set of hypotheses. -/
theorem qlink6_sound_lanes {P : List PE6} {os : List Open6Q} {lay : Layout6} {ws : List Word} {c : Ctx}
    {M : Mem} (hS : streamOkL6 P = true) (hP2 : 2 ≤ P.length) (hO : opensOK P os = true)
    (hQ : qOk6 P os lay = true) (hin : QIn6 P os lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink6 P os lay pt).2) (hA : SegsAssert M pt (qlink6 P os lay pt).2) :
    QLinkConcl P (Lvm.QSig.digAt M.k lay.cp) ws ∧ LaneLink6 P (Lvm.QSig.digAt M.k lay.cp) ws :=
  ⟨qlink6_sound hS hP2 hO hQ hin hws hinj hN hNs h hA,
    (qlink6_lanes hS hP2 hO (qOk6_sound hQ) hin hws hinj hN hNs h hA).1⟩

end Lvm6.Q
