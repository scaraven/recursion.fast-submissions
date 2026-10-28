-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12b, track L-circ).
import FRNodeRows4

/-!
# The 4.1 nodes' plan and `evalM`: one evaluation per prototype

**The plan** (`planOf4`, a closed constant built at process start, B-16) is the two prototypes'
proved pieces (S-E13's construction for one slot: `protoData`, `protoData_rows`), shared by `N2`,
`N4` and `N8`.

**`evalM`** (`evalMT4`). Every entry of slot `σ`'s rows has its row and its cell in region `σ`, so
for the prototype's rows moved to region `σ` and made absolute (`copy_val`):

  `MLE(slot σ)(τ, u) = eq(τ_[20,lm), σ) · eq(u_[20,lm), σ) · u_lm · u_lm+1 · MLE_lo(prototype)`

where `MLE_lo` is the prototype's value at the point restricted to region `π`'s low coordinates
(`starPt`): one evaluation per prototype, by the existing templated evaluator (21 row and 23 cell
coordinates), whatever the kind. The link rows (≤ 7 per slot) are summed directly. The region
facts are checked once per process on the pieces (`pieceInB`, `pcIn_spec`), with the sparse sum as
the fallback. **`evalMT4_eq`**: `evalMT4` is the MLE of `nodeIRows4 κ`'s three matrices.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## The two prototypes' pieces (S-E13's `planData`, two programs) -/

/-- Prototype `π`'s `one` form. -/
abbrev oneP (π : ℕ) : Lin := Lin.cell (oneR π)

theorem infoOf_map (ks : List TKey) (k : TKey) :
    infoOf (ks.map mkKM) k = ((tRows k).length, cregion k, tNlocs k) := by
  rw [infoOf, kmOf_map, mkKM_info]

/-- **The plan's data**: both prototypes compiled with one template memo, laid out with one key
table, their proto-pieces, **one grouping** (so that the keys, and their preparation in `evalM`,
are shared), each prototype's checked pieces. -/
def planData4 : Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece :=
  let ops0 := (protoProg 0).ops
  let ops1 := (protoProg 1).ops
  let z0 := compMS [] (protoP 0) [] (CS.init (baseR 0)) ops0 none []
  let z1 := compMS [] (protoP 1) z0.2.2 (CS.init (baseR 1)) ops1 none []
  -- both prototypes' keys (a closure over `z0` here would be specialised into the loop and
  -- recompute the compile per key: measured 10 s at process start)
  let kms := ((keyCounts (z1.1.tins ++ z0.1.tins)).map Prod.fst).map mkKM
  let l0 := mkLayI (infoOf kms) z0.1.nrows z0.1.next (keyCounts z0.1.tins)
  let l1 := mkLayI (infoOf kms) z1.1.nrows z1.1.next (keyCounts z1.1.tins)
  let r0 := compMS l0 (protoP 0) z1.2.2 (CS.init (baseR 0)) ops0 none []
  let r1 := compMS l1 (protoP 1) r0.2.2 (CS.init (baseR 1)) ops1 none []
  let p0 := slotRP (oneP 0) kms l0 0 r0.1 r0.2.1.reverse []
  let rps1 := (slotRP (oneP 1) kms l1 (1 * slotM4) r1.1 r1.2.1.reverse p0.2).1
  let g := groupRP p0.1 rps1
  (g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 (oneP 0) p0.1 g.2.2.2.1, piecesOf g.1 g.2.2.1 (oneP 1) rps1 g.2.2.2.2)

/-- **The pieces are the prototypes' rows.** -/
theorem planData4_rows :
    planData4.2.2.2.1.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.1 (oneP 0)) = protoRows 0 ∧
      planData4.2.2.2.2.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.2.1 (oneP 1)) = protoRows 1 := by
  simp only [planData4, piecesOf_rows]
  obtain ⟨hz0, mz0⟩ := compMS_T [] (protoP 0) (baseR 0) (protoProg 0).ops (M := []) (by simp [MOk])
  obtain ⟨hz1, mz1⟩ := compMS_T [] (protoP 1) (baseR 1) (protoProg 1).ops mz0
  rw [mkLayI_eq _ (infoOf_map _), mkLayI_eq _ (infoOf_map _), hz0, hz1, ← layOf, ← layOf]
  obtain ⟨hr0, mr0⟩ := compMS_T (layOf (protoP 0) (baseR 0) (protoProg 0).ops) (protoP 0) (baseR 0)
    (protoProg 0).ops mz1
  obtain ⟨hr1, -⟩ := compMS_T (layOf (protoP 1) (baseR 1) (protoProg 1).ops) (protoP 1) (baseR 1)
    (protoProg 1).ops mr0
  rw [slotRP_rows, slotRP_rows, hr0, hr1, protoRows, protoRows, protoCS, protoCS, protoLay, protoLay]
  exact ⟨rfl, by rw [one_mul]⟩

/-! ## The region check -/

/-- A cell of region `π`. -/
def inSB (π c : ℕ) : Bool := decide (π * slotM4 ≤ c) && decide (c < π * slotM4 + slotM4)
/-- A form over region `π`'s cells. -/
def linInB (π : ℕ) (l : Lin) : Bool := l.all fun t => inSB π t.1
/-- A row index of region `π`, below its link rows. -/
def idxInB (π r : ℕ) : Bool := decide (π * slotM4 ≤ r) && decide (r + 8 < π * slotM4 + slotM4)

/-- **A piece stays in region `π`** (its rows below the link rows, its cells in the region). -/
def pieceInB (keys : Array Key) (sh : Array (List Lin)) (one : Lin) (π : ℕ) : Piece → Bool
  | .sp rs => rs.all fun p => idxInB π p.1 && linInB π p.2.a && linInB π p.2.b && linInB π p.2.c
  | .ins k xh ch own =>
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).A * xh) &&
    decide (2 ^ (keys.getD k dkey).A * xh + (keys.getD k dkey).rows.length + 8 ≤ π * slotM4 + slotM4) &&
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).B * ch) &&
    decide (2 ^ (keys.getD k dkey).B * ch + 2 ^ (keys.getD k dkey).B ≤ π * slotM4 + slotM4) &&
    linInB π one && (sh.getD k [] ++ own).all (linInB π)

/-- **Rows of region `π`**: indices below its link rows, every cell of every matrix in it. -/
def InSlot (π : ℕ) (rows : List (ℕ × Row)) : Prop :=
  ∀ p ∈ rows, (π * slotM4 ≤ p.1 ∧ p.1 + 8 < π * slotM4 + slotM4) ∧
    ∀ s : Mat, ∀ t ∈ s.r p.2, π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4

theorem linInB_spec {π : ℕ} {l : Lin} (h : linInB π l = true) {t : ℕ × F} (ht : t ∈ l) :
    π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4 := by
  have := List.all_eq_true.1 h t ht
  simpa [inSB] using this

theorem mem_smul {c : F} {l : Lin} {t : ℕ × F} (h : t ∈ l.smul c) : ∃ t' ∈ l, t.1 = t'.1 := by
  simp only [Lin.smul, List.mem_map] at h
  obtain ⟨t', ht', rfl⟩ := h
  exact ⟨t', ht', rfl⟩

theorem pieceInB_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : Piece} (h : pieceInB keys sh one π pc = true) :
    InSlot π (Piece.rows keys sh one pc) := by
  cases pc with
  | sp rs =>
    intro p hp
    have := List.all_eq_true.1 h p hp
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hc⟩ := this
    refine ⟨by simpa [idxInB] using hi, fun s t ht => ?_⟩
    cases s
    · exact linInB_spec ha ht
    · exact linInB_spec hb ht
    · exact linInB_spec hc ht
  | ins k xh ch own =>
    simp only [pieceInB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨-, -, -, hloc⟩ := Key.ok_spec (key_ok hk k)
    intro p hp
    simp only [Piece.rows, instIR, List.mem_map] at hp
    obtain ⟨⟨r, i⟩, hri, rfl⟩ := hp
    have hri' := List.mk_mem_zipIdx_iff_getElem?.1 hri
    obtain ⟨hil, hr⟩ := List.getElem?_eq_some_iff.1 hri'
    have hrm : r ∈ (keys.getD k dkey).rows := hr ▸ List.getElem_mem hil
    refine ⟨⟨by omega, by omega⟩, fun s t ht => ?_⟩
    rw [Mat.r_inst] at ht
    simp only [instLin, List.mem_flatMap] at ht
    obtain ⟨⟨w, c⟩, hw, ht⟩ := ht
    cases w with
    | one =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]; exact linInB_spec h5 ht'
    | inp j =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]
      have hm : (sh.getD k [] ++ own).getD j [] ∈ (sh.getD k [] ++ own) ∨
          (sh.getD k [] ++ own).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD]
        rcases hj : (sh.getD k [] ++ own)[j]? with _ | l
        · exact Or.inr rfl
        · exact Or.inl (List.mem_of_getElem? hj)
      rcases hm with hm | hm
      · exact linInB_spec (List.all_eq_true.1 h6 _ hm) ht'
      · rw [hm] at ht'; simp at ht'
    | loc j =>
      simp only [List.mem_singleton] at ht
      subst ht
      have := hloc s r hrm j c hw
      dsimp only
      constructor <;> omega

theorem pcIn_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : List Piece} (h : pc.all (pieceInB keys sh one π) = true) :
    InSlot π (pc.flatMap (Piece.rows keys sh one)) := by
  intro p hp
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.1 hp
  exact pieceInB_spec hk (List.all_eq_true.1 h q hq) p hp

/-- **`t` restricted to region `π`'s low coordinates**: `t` below 20, `π`'s bit at 20, `0` above
(so that `eq(starPt t π, π·2^20 + j) = eq(t_<20, j)`). -/
def starPt (t : ℕ → F) (π : ℕ) (l : ℕ) : F := if l < 20 then t l else if l = 20 then (if π = 1 then 1 else 0) else 0

/-! ## The plan -/

/-- Every key's rows and locals fit 20 bits (so its preparation reads coordinates below 20 only,
which both prototypes' points share: `kprep_star`). -/
def lowKeys (keys : Array Key) : Bool := keys.all fun K => decide (K.A ≤ 20) && decide (K.B ≤ 20)

/-- **The 4.1 nodes' plan** (all of `N2`, `N4`, `N8`): the shared keys, each prototype's shared
forms and pieces (its rows, `ok`), the prepared forms, and the checks. -/
structure Plan4 where
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
    pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  pats : Array (Array Pat)
  pbs : List ℕ
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  hp0 : p0 = pc0.map (prepPiece pats)
  hp1 : p1 = pc1.map (prepPiece pats)
  inR : Bool
  hR : inR = true → InSlot 0 (protoRows 0) ∧ InSlot 1 (protoRows 1) ∧ lowKeys keys = true

/-- A plan from its pieces (the region and key checks computed here, once). -/
def mkPlan4 (keys : Array Key) (sh0 sh1 : Array (List Lin)) (pc0 pc1 : List Piece)
    (pats : Array (Array Pat))
    (ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
      pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1) : Plan4 where
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  p0 := pc0.map (prepPiece pats)
  p1 := pc1.map (prepPiece pats)
  pats := pats
  pbs := patBits pats
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl
  inR := pc0.all (pieceInB keys sh0 (oneP 0) 0) && pc1.all (pieceInB keys sh1 (oneP 1) 1) && lowKeys keys
  hR := fun h => by
    simp only [Bool.and_eq_true] at h
    exact ⟨ok.2.1 ▸ pcIn_spec ok.1 h.1.1, ok.2.2 ▸ pcIn_spec ok.1 h.1.2, h.2⟩

def planOf4D (d : Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece)
    (hd : d = planData4) : Plan4 :=
  if h : (d.1.map mkKey).all (Key.ok 21) = true then
    mkPlan4 (d.1.map mkKey) d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats (d.1.map mkKey).size (d.2.2.2.1 ++ d.2.2.2.2))
      ⟨h, by subst hd; exact planData4_rows.1, by subst hd; exact planData4_rows.2⟩
  else
    -- the fallback's rows depend on `d` (`protoRows (k − k)`), so that the compiler does not hoist
    -- `protoRows 0` into a closed constant built at every process start (S-E13's kernel and init traps)
    mkPlan4 #[] #[] #[] [.sp (protoRows (d.1.size - d.1.size))] [.sp (protoRows (d.1.size - d.1.size + 1))] #[]
      ⟨by simp, by rw [Nat.sub_self]; exact List.flatMap_singleton .., by rw [Nat.sub_self]; exact List.flatMap_singleton ..⟩

/-- **The 4.1 nodes' plan, built once per process** (B-16): from proved pieces, no run-time row
comparison. -/
def planOf4 : Plan4 := planOf4D planData4 rfl

/-! ## A prototype's value -/

/-- The evaluation tables of a prototype's point. -/
def tb4 (pl : Plan4) (π : ℕ) (t u : ℕ → F) : Tb :=
  tbOf 21 t u (oneP π) (needAll pl.keys (·.A) 12) (needAll pl.keys (·.B) 13 pl.pbs)
    (needAll pl.keys (·.A) 22) (needAll pl.keys (·.B) 24 pl.pbs)

theorem loTab_congr {A : ℕ} {t t' : ℕ → F} (h : ∀ l < A, t l = t' l) : loTab A t = loTab A t' := by
  unfold loTab; congr 1; exact List.map_congr_left fun l hl => h l (List.mem_range.1 hl)

/-- **A key's preparation reads coordinates below its bits only.** -/
theorem kprep_star (s : Mat) (t u : ℕ → F) (π π' : ℕ) {K : Key} (hA : K.A ≤ 20) (hB : K.B ≤ 20) :
    kprep s (starPt t π) (starPt u π) K = kprep s (starPt t π') (starPt u π') K := by
  unfold kprep
  rw [loTab_congr (t := starPt t π) (t' := starPt t π') (fun l hl => by simp [starPt, show l < 20 by omega]),
    loTab_congr (t := starPt u π) (t' := starPt u π') (fun l hl => by simp [starPt, show l < 20 by omega])]

theorem kp_shared (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) :
    pl.keys.map (kprep3 (tb4 pl 0 (starPt t 0) (starPt u 0)) (starPt t 0) (starPt u 0)) =
      pl.keys.map (kprep3 (tb4 pl 1 (starPt t 1) (starPt u 1)) (starPt t 1) (starPt u 1)) := by
  refine Array.map_congr_left fun K hK => ?_
  have h := Array.all_eq_true_iff_forall_mem.1 hk K hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [tb4, kprep3_eq, kprep_star _ t u 0 1 h.1 h.2]

/-- **The two prototypes' values at `(t, u)`**: one key preparation, each prototype at its point. -/
def protoV4 (pl : Plan4) (t u : ℕ → F) (node : Bool) : F3 × F3 :=
  let t0 := starPt t 0; let u0 := starPt u 0; let t1 := starPt t 1; let u1 := starPt u 1
  let tb0 := tb4 pl 0 t0 u0
  let kp := pl.keys.map (kprep3 tb0 t0 u0)
  (if node then slotV3 (ectx3 21 tb0 t0 u0 pl.keys kp pl.g0 pl.pats) pl.p0 else (0, 0, 0),
   slotV3 (ectx3 21 (tb4 pl 1 t1 u1) t1 u1 pl.keys kp pl.g1 pl.pats) pl.p1)

/-- The three matrices of rows, sparse. -/
def rows3 (n m : ℕ) (t u : ℕ → F) (rows : List (ℕ × Row)) : F3 :=
  (rowsVal (RingHom.id F) .a n m t u rows, rowsVal (RingHom.id F) .b n m t u rows,
    rowsVal (RingHom.id F) .c n m t u rows)

theorem protoV4_eq (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) (node : Bool) :
    (protoV4 pl t u node).1 = (if node then rows3 21 23 (starPt t 0) (starPt u 0) (protoRows 0) else (0, 0, 0)) ∧
      (protoV4 pl t u node).2 = rows3 21 23 (starPt t 1) (starPt u 1) (protoRows 1) := by
  simp only [protoV4]
  refine ⟨?_, ?_⟩
  · split_ifs
    · simp only [tb4, slotV3_eq]
      rw [pl.hg0, pl.hp0]
      simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.1, rows3]
    · rfl
  · rw [kp_shared pl hk]
    simp only [tb4, slotV3_eq]
    rw [pl.hg1, pl.hp1]
    simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.2, rows3]

/-! ## The copy identity -/

theorem eqN_congr {n : ℕ} {t t' : ℕ → F} (h : ∀ l < n, t l = t' l) (x : ℕ) : eqN n t x = eqN n t' x :=
  Finset.prod_congr rfl fun l hl => by rw [h l (Finset.mem_range.1 hl)]

theorem gN_star {π n : ℕ} (hπ : π ≤ 1) (hn : 21 ≤ n) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN n (starPt t π) (π * slotM4 + j) = eqN 20 t j := by
  have e : π * slotM4 + j = 2 ^ 20 * π + j := by simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hj]
  have h1 : eqN 20 (starPt t π) j = eqN 20 t j := eqN_congr (fun l hl => by simp [starPt, hl]) j
  have h2 : gN (n - 20) (fun l => starPt t π (20 + l)) π = 1 := by
    have hp : π < 2 ^ (n - 20) := lt_of_le_of_lt hπ (Nat.one_lt_two_pow (by omega))
    rw [gN, if_pos hp]; unfold eqN
    refine Finset.prod_eq_one fun l _ => ?_
    rcases Nat.lt_or_ge l 1 with h0 | h0
    · obtain rfl : l = 0 := by omega
      interval_cases π <;> simp [starPt]
    · have hb : π.testBit l = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hπ
        (lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) h0)))
      simp only [hb, Bool.false_eq_true, if_false, starPt, show ¬ 20 + l < 20 by omega,
        show 20 + l ≠ 20 by omega, sub_zero]
  rw [h1, h2, mul_one]

/-- The high factor of slot `σ`: `eq(t_[20,lm), σ)`. -/
def hiF (lm : ℕ) (t : ℕ → F) (σ : ℕ) : F := eqN (lm - 20) (fun l => t (20 + l)) σ

theorem gN_row {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN lm t (σ * slotM4 + j) = eqN 20 t j * hiF lm t σ := by
  have e : σ * slotM4 + j = 2 ^ 20 * σ + j := by simp only [slotM4]; ring
  rw [e, gN_split hl _ _ hj, gN, if_pos hσ, hiF]

theorem gN_two (v : ℕ → F) : gN 2 v 3 = v 0 * v 1 := by
  rw [gN, if_pos (by norm_num), eqN]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp only [show (3 : ℕ).testBit 0 = true by decide, show (3 : ℕ).testBit 1 = true by decide, if_true]

theorem gN_cell {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F) {x : ℕ} (hx : x < 2 ^ 20) :
    gN (lm + 2) u (σ * slotM4 + x + 3 * 2 ^ lm) = eqN 20 u x * (hiF lm u σ * (u lm * u (lm + 1))) := by
  have e : σ * slotM4 + x + 3 * 2 ^ lm = 2 ^ 20 * (2 ^ (lm - 20) * 3 + σ) + x := by
    rw [show 2 ^ lm = 2 ^ 20 * 2 ^ (lm - 20) by rw [← pow_add]; congr 1; omega]; simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hx, gN_split (by omega) _ _ hσ, hiF]
  have e2 : lm + 2 - 20 - (lm - 20) = 2 := by omega
  rw [e2, gN_two]
  have e3 : 20 + (lm - 20 + 0) = lm := by omega
  have e4 : 20 + (lm - 20 + 1) = lm + 1 := by omega
  simp only [e3, e4]

theorem r_rowMapC (s : Mat) (f : ℕ → ℕ) (r : Row) : s.r (rowMapC f r) = mapC f (s.r r) := by cases s <;> rfl

/-- One entry of a moved, absolute row against the prototype's. -/
theorem copy_term {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F)
    {q : ℕ × F} (hq : π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    q.2 * gN (lm + 2) u (mvC π σ q.1 + 3 * 2 ^ lm) =
      (hiF lm u σ * (u lm * u (lm + 1))) * (q.2 * gN 23 (starPt u π) q.1) := by
  obtain ⟨hq1, hq2⟩ := hq
  have hx : q.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have ec : mvC π σ q.1 + 3 * 2 ^ lm = σ * slotM4 + (q.1 - π * slotM4) + 3 * 2 ^ lm := by
    simp only [mvC]; omega
  have eq' : gN 23 (starPt u π) q.1 = gN 23 (starPt u π) (π * slotM4 + (q.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' hq1]
  rw [ec, gN_cell hl hσ u hx, eq', gN_star hπ (by norm_num) u hx]
  ring

/-- **One moved, absolute row** against the prototype's. -/
theorem copy_row {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {p : ℕ × Row} (hp : (π * slotM4 ≤ p.1 ∧ p.1 + 8 < π * slotM4 + slotM4) ∧
      ∀ s' : Mat, ∀ q ∈ s'.r p.2, π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    gN lm t (mvC π σ p.1) * linE (RingHom.id F) (lm + 2) u
        (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) *
        (gN 21 (starPt t π) p.1 * linE (RingHom.id F) 23 (starPt u π) (s.r p.2)) := by
  obtain ⟨⟨h1, h2⟩, hc⟩ := hp
  have hj : p.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have er : mvC π σ p.1 = σ * slotM4 + (p.1 - π * slotM4) := by simp only [mvC]; omega
  have ep : gN 21 (starPt t π) p.1 = gN 21 (starPt t π) (π * slotM4 + (p.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' h1]
  have hL : linE (RingHom.id F) (lm + 2) u (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm u σ * (u lm * u (lm + 1))) * linE (RingHom.id F) 23 (starPt u π) (s.r p.2) := by
    rw [r_rowMapC, r_rowMapC]
    simp only [linE, mapC, List.map_map, Function.comp_def, RingHom.id_apply]
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    exact copy_term hπ hl hσ u (hc s q hq)
  rw [er, gN_row hl hσ t hj, hL, ep, gN_star hπ (le_refl _) t hj]
  ring

/-- **A slot's value is its prototype's, scaled** (the region facts given). -/
theorem copy_val {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {rows : List (ℕ × Row)} (hR : InSlot π rows) :
    rowsVal (RingHom.id F) s lm (lm + 2) t u
        ((mvRows π σ rows).map fun p => (p.1, rowMapC (· + 3 * 2 ^ lm) p.2)) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) * rowsVal (RingHom.id F) s 21 23 (starPt t π) (starPt u π) rows := by
  simp only [rowsVal, mvRows, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p hp => copy_row hπ hl hσ s t u (hR p hp))

/-! ## `evalM` -/

/-- `c · x` over triples. -/
def smul3 (c : F) (x : F3) : F3 := (c * x.1, c * x.2.1, c * x.2.2)

/-- **Slot `σ`'s value** from its prototype's (`vN`, `vS`): link rows sparse, the rest scaled. -/
def slotV4 (κ : NodeKind) (t u : ℕ → F) (vN vS : F3) (σ : ℕ) : F3 :=
  let lm := κ.dims.logM
  add3 (rows3 lm (lm + 2) t u (linkIRows4 κ σ))
    (smul3 (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) (if protoOf κ σ = 0 then vN else vS))

/-- A prototype's rows from the plan's pieces (the fallback's; no closed `protoRows` constant in
the compiled code). -/
def protoRowsP (pl : Plan4) (π : ℕ) : List (ℕ × Row) :=
  if π = 0 then pl.pc0.flatMap (Piece.rows pl.keys pl.sh0 (oneP 0))
  else pl.pc1.flatMap (Piece.rows pl.keys pl.sh1 (oneP 1))

/-- `nodeIRows4` from the plan's pieces. -/
def nodeIRowsP (pl : Plan4) (κ : NodeKind) : List (ℕ × Row) :=
  (List.range κ.vslots).flatMap fun σ =>
    linkIRows4 κ σ ++ absRows4 κ (mvRows (protoOf κ σ) σ (protoRowsP pl (protoOf κ σ)))

theorem nodeIRowsP_eq (pl : Plan4) (κ : NodeKind) : nodeIRowsP pl κ = nodeIRows4 κ := by
  have h : ∀ σ, protoRowsP pl (protoOf κ σ) = protoRows (protoOf κ σ) := fun σ => by
    unfold protoRowsP protoOf; split_ifs <;> simp_all [pl.ok.2.1, pl.ok.2.2]
  simp only [nodeIRowsP, nodeIRows4, slotRows4, h]

/-- **`evalM` of a 4.1 node** (S-E12b): the two prototypes' values once, every slot from them;
the sparse sum over `nodeIRows4 κ` if a region check failed. -/
def evalMT4 (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : F3 :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  if pl.inR then
    let v := protoV4 pl t u κ.hasPrev
    sum3 (slotV4 κ t u v.1 v.2) (List.range κ.vslots)
  else rows3 κ.dims.logM (κ.dims.logM + 2) t u (nodeIRowsP pl κ)

/-- **`evalM`'s specification**: the MLEs of `nodeIRows4 κ`'s matrices (`τ`: `logM` coordinates,
`σ`: `m − 7 = logM + 2`). -/
noncomputable def evalMS4 (κ : NodeKind) (τ σ : Array F) : F3 :=
  (Eval.matMLE (entriesI .a (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .b (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .c (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ))

theorem logM_ge (κ : NodeKind) : 20 ≤ κ.dims.logM ∧ κ.vslots ≤ 2 ^ (κ.dims.logM - 20) := by
  cases κ <;> decide

theorem rows3_append (n m : ℕ) (t u : ℕ → F) (a b : List (ℕ × Row)) :
    rows3 n m t u (a ++ b) = add3 (rows3 n m t u a) (rows3 n m t u b) := by
  simp [rows3, add3, rowsVal_append]

theorem sum3_congr {f g : ℕ → F3} {l : List ℕ} (h : ∀ x ∈ l, f x = g x) : sum3 f l = sum3 g l := by
  simp only [sum3_eq, sumL_eq]
  rw [List.map_congr_left fun x hx => congrArg Prod.fst (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.1) (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.2) (h x hx)]

theorem rows3_flatMap (n m : ℕ) (t u : ℕ → F) (l : List ℕ) (f : ℕ → List (ℕ × Row)) :
    rows3 n m t u (l.flatMap f) = sum3 (fun σ => rows3 n m t u (f σ)) l := by
  simp only [rows3, sum3_eq, sumL_eq, rowsVal_flatMap]

/-- **`evalM_eq` for the 4.1 nodes.** -/
theorem evalMT4_eq (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : evalMT4 pl κ τ σ = evalMS4 κ τ σ := by
  have hspec : rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0) (nodeIRows4 κ) =
      evalMS4 κ τ σ := by
    simp only [rows3, evalMS4, rowsVal_F, Eval.sparse_eq]
  unfold evalMT4
  dsimp only
  by_cases hR : pl.inR = true
  · rw [if_pos hR, ← hspec, nodeIRows4, rows3_flatMap]
    obtain ⟨hR0, hR1, hk⟩ := pl.hR hR
    obtain ⟨hl, hv⟩ := logM_ge κ
    obtain ⟨hv0, hv1⟩ := protoV4_eq pl hk (fun l => τ.getD l 0) (fun l => σ.getD l 0) κ.hasPrev
    refine sum3_congr fun s hs => ?_
    have hs' : s < 2 ^ (κ.dims.logM - 20) := lt_of_lt_of_le (List.mem_range.1 hs) hv
    rw [rows3_append, slotV4]
    refine congrArg (add3 _) ?_
    have hc : ∀ π : ℕ, π ≤ 1 → InSlot π (protoRows π) →
        smul3 (hiF κ.dims.logM (fun l => τ.getD l 0) s * (hiF κ.dims.logM (fun l => σ.getD l 0) s *
            (σ.getD κ.dims.logM 0 * σ.getD (κ.dims.logM + 1) 0)))
          (rows3 21 23 (starPt (fun l => τ.getD l 0) π) (starPt (fun l => σ.getD l 0) π) (protoRows π)) =
        rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0)
          (absRows4 κ (mvRows π s (protoRows π))) := by
      intro π hπ hr
      have hab : absRows4 κ (mvRows π s (protoRows π)) =
          (mvRows π s (protoRows π)).map fun p => (p.1, rowMapC (· + 3 * 2 ^ κ.dims.logM) p.2) := by
        simp only [absRows4, oneCell_eq]
      rw [hab]
      simp only [smul3, rows3, copy_val hπ hl hs' _ (fun l => τ.getD l 0) (fun l => σ.getD l 0) hr]
    simp only [slotRows4]
    by_cases hp : protoOf κ s = 0
    · have hk' : κ.hasPrev = true := by
        by_contra hk'; simp [protoOf, isPrevSlot, hk'] at hp
      rw [if_pos hp, hv0, if_pos hk', hp]
      exact hc 0 (by norm_num) hR0
    · have h1 : protoOf κ s = 1 := by
        simp only [protoOf] at hp ⊢; split_ifs at hp ⊢ <;> simp_all
      rw [if_neg hp, hv1, h1]
      exact hc 1 le_rfl hR1
  · rw [if_neg hR, nodeIRowsP_eq]; exact hspec

/-! ## Controls -/

/-- (+) `starPt` keeps the low coordinates and sets coordinate 20 to the region's bit; (−) it drops
the coordinates above. -/
theorem star_ctl (t : ℕ → F) : starPt t 1 3 = t 3 ∧ starPt t 1 20 = 1 ∧ starPt t 0 20 = 0 ∧ starPt t 1 21 = 0 := by
  simp [starPt]

/-- (+) A piece inside region 1 passes the check; (−) one whose cell lies in region 0 fails. -/
theorem pieceInB_ctl :
    pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(2 ^ 20 + 1, 1)], [], []⟩)]) = true ∧
      pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(5, 1)], [], []⟩)]) = false := by
  constructor <;> decide

end Rev4
end FR
