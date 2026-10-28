-- New for `flock-recursive` (BLUEPRINT §10 changes 22 (d), revision 3.15; stage S-E11, track
-- L-circ).
import FRVIRTplGrp

/-!
# The evaluator's run class and the fast key preparation

BLUEPRINT §10 changes 22 (d). Two changes to `evalM`'s cost, neither to its value:

* **Runs** (the per-chunk aligned-shift input class). An instance's own inputs `j … j + len − 1`
  whose forms are the cells `2^B·ch + r + t` (`t < len`, `r + len ≤ 2^B`) contribute
  `Σ_t U[j + t]·eq(σ, 2^B·ch + r + t) = eq(σ_{≥B}, ch) · Σ_t U[j + t]·eq(σ_{<B}, r + t)`
  (`gN_split`). The inner sum depends only on the key's **pattern** `(j, r, len, B)`, so it is
  computed once per key and slot (`runIn`); an instance pays one `hfac` per run. `prepOwn` emits a
  run only where the forms check (`runCh`): correctness does not depend on the pattern table, which
  the plan's search (`patsFor`, untrusted) builds from the instances.
* **The keys' preparation** (`kprepF`): one product per row and matrix (the row factor times the
  row's local sum), none for a unit coefficient (characteristic 2: `−1 = 1`), and the `eq` tables
  of the keys' bits built once per evaluation (`preTabs`). `kprepF_eq`: it is `kprepT`.
-/

namespace FR
namespace TEval
open Circ Tpl

/-! ## The fast key preparation -/

/-- `w · x`, with no product when `x = 0`. -/
@[inline] def mulNZ (w x : F) : F := if x == 0 then 0 else w * x

theorem mulNZ_eq (w x : F) : mulNZ w x = w * x := by
  unfold mulNZ; split_ifs with h
  · rw [beq_iff_eq.1 h, mul_zero]
  · rfl

/-- A row form's local part `Σ c · eσ(k)`. -/
def locRow (eσ : ℕ → F) (l : LinT) : F :=
  sumL (fun t => match t.1 with | .loc k => cmulF t.2 (eσ k) | _ => 0) l

/-- A row form's `one` part. -/
def oneRow (l : LinT) : F := sumL (fun t => match t.1 with | .one => t.2 | _ => 0) l

def inpStep (m : ℕ) (t : Wire × F) : ℕ := match t.1 with | .inp i => max m (i + 1) | _ => m

/-- The number of input indices matrix `s` of the rows reads. -/
def inpN (s : Mat) (T : List RowT) : ℕ := T.zipIdx.foldl (fun m p => (s.t p.1).foldl inpStep m) 0

def uStep (w : F) (U : Array F) (t : Wire × F) : Array F :=
  match t.1 with | .inp i => U.modify i (· + cmulF t.2 w) | _ => U

/-- The dense input coefficients, row by row. -/
def inpU (s : Mat) (T : List RowT) (eτ : ℕ → F) : Array F :=
  T.zipIdx.foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) (Array.replicate (inpN s T) 0)

/-- **A key's preparation, fast.** -/
def kprepF (s : Mat) (eτ eσ : ℕ → F) (K : Key) : KP :=
  ⟨sumL (fun p => mulNZ (eτ p.2) (locRow eσ (s.t p.1))) K.rows.zipIdx,
   sumL (fun p => mulNZ (eτ p.2) (oneRow (s.t p.1))) K.rows.zipIdx, inpU s K.rows eτ⟩

/-- The input terms of rows `L`, by matrix `s` and row factor `eτ`. -/
abbrev ttL (s : Mat) (eτ : ℕ → F) (L : List (RowT × ℕ)) : List (Wire × F) :=
  L.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * t.2)

theorem inpList_append (a b : List (Wire × F)) : inpList (a ++ b) = inpList a ++ inpList b := by
  simp [inpList, List.filterMap_append]

theorem foldl_inpN_row (w : F) : ∀ (l : LinT) (m : ℕ),
    (inpList (l.map fun t => (t.1, w * t.2))).foldl (fun m q => max m (q.1 + 1)) m = l.foldl inpStep m
  | [], _ => rfl
  | ⟨wi, c⟩ :: l, m => by
    cases wi <;> simp only [List.map_cons, inpList, List.filterMap_cons, List.foldl_cons, inpStep] <;>
      exact foldl_inpN_row w l _

theorem foldl_inpN (s : Mat) (eτ : ℕ → F) : ∀ (L : List (RowT × ℕ)) (m : ℕ),
    (inpList (ttL s eτ L)).foldl (fun m q => max m (q.1 + 1)) m =
      L.foldl (fun m p => (s.t p.1).foldl inpStep m) m
  | [], _ => rfl
  | p :: L, m => by
    rw [ttL, List.flatMap_cons, inpList_append, List.foldl_append, foldl_inpN_row, List.foldl_cons]
    exact foldl_inpN s eτ L _

theorem foldl_inpU_row (w : F) : ∀ (l : LinT) (U : Array F),
    (inpList (l.map fun t => (t.1, w * t.2))).foldl (fun U q => U.modify q.1 (· + q.2)) U =
      l.foldl (uStep w) U
  | [], _ => rfl
  | ⟨wi, c⟩ :: l, U => by
    cases wi <;> simp only [List.map_cons, inpList, List.filterMap_cons, List.foldl_cons, uStep]
    · exact foldl_inpU_row w l _
    · rw [cmulF_eq, mul_comm c w]; exact foldl_inpU_row w l _
    · exact foldl_inpU_row w l _

theorem foldl_inpU (s : Mat) (eτ : ℕ → F) : ∀ (L : List (RowT × ℕ)) (U : Array F),
    (inpList (ttL s eτ L)).foldl (fun U q => U.modify q.1 (· + q.2)) U =
      L.foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) U
  | [], _ => rfl
  | p :: L, U => by
    rw [ttL, List.flatMap_cons, inpList_append, List.foldl_append, foldl_inpU_row, List.foldl_cons]
    exact foldl_inpU s eτ L _

theorem ttR_id (s : Mat) (T : List RowT) (eτ : ℕ → F) : ttR (RingHom.id F) s T eτ = ttL s eτ T.zipIdx := by
  simp [ttR, ttL]

theorem locSum_append (eσ : ℕ → F) (a b : List (Wire × F)) :
    locSum eσ (a ++ b) = locSum eσ a + locSum eσ b := by simp [locSum]

theorem oneSum_append (a b : List (Wire × F)) : oneSum (a ++ b) = oneSum a + oneSum b := by
  simp [oneSum]

theorem locRow_eq (eσ : ℕ → F) (w : F) (l : LinT) :
    locSum eσ (l.map fun t => (t.1, w * t.2)) = mulNZ w (locRow eσ l) := by
  rw [mulNZ_eq, locRow, sumL_eq, ← List.sum_map_mul_left, locSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun ⟨wi, c⟩ _ => ?_)
  cases wi <;> simp [cmulF_eq, mul_assoc]

theorem oneRow_eq (w : F) (l : LinT) :
    oneSum (l.map fun t => (t.1, w * t.2)) = mulNZ w (oneRow l) := by
  rw [mulNZ_eq, oneRow, sumL_eq, ← List.sum_map_mul_left, oneSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun ⟨wi, c⟩ _ => ?_)
  cases wi <;> simp

theorem locSum_ttL (s : Mat) (eτ eσ : ℕ → F) : ∀ L : List (RowT × ℕ),
    locSum eσ (ttL s eτ L) = (L.map fun p => mulNZ (eτ p.2) (locRow eσ (s.t p.1))).sum
  | [] => rfl
  | p :: L => by rw [ttL, List.flatMap_cons, locSum_append, locRow_eq, ← ttL, locSum_ttL s eτ eσ L]; rfl

theorem oneSum_ttL (s : Mat) (eτ : ℕ → F) : ∀ L : List (RowT × ℕ),
    oneSum (ttL s eτ L) = (L.map fun p => mulNZ (eτ p.2) (oneRow (s.t p.1))).sum
  | [] => rfl
  | p :: L => by rw [ttL, List.flatMap_cons, oneSum_append, oneRow_eq, ← ttL, oneSum_ttL s eτ L]; rfl

/-- **`kprepF` is `kprepT`.** -/
theorem kprepF_eq (s : Mat) (eτ eσ : ℕ → F) (K : Key) : kprepF s eτ eσ K = kprepT s eτ eσ K := by
  simp only [kprepF, kprepT, ttR_id]
  congr 1
  · rw [locSum_ttL, sumL_eq]
  · rw [oneSum_ttL, sumL_eq]
  · rw [denseIT, inpU, inpN, foldl_inpN, foldl_inpU]

/-! ## The three matrices' preparations in one pass (S-T1) -/

/-- One matrix's running preparation `(loc, one, U)`. -/
abbrev KS := F × F × Array F

/-- One term of a row form: its local part, its `one` part, its input coefficient (row factor `w`). -/
@[inline] def tStep (eσ : ℕ → F) (w : F) (x : KS) (t : Wire × F) : KS :=
  match t.1 with
  | .loc k => (x.1 + cmulF t.2 (eσ k), x.2.1, x.2.2)
  | .one => (x.1, x.2.1 + t.2, x.2.2)
  | .inp i => (x.1, x.2.1, x.2.2.modify i (· + cmulF t.2 w))

/-- Row `r` (row factor `w`) added to matrix `s`'s running preparation, its form read once. -/
@[inline] def kp1 (s : Mat) (eσ : ℕ → F) (w : F) (r : RowT) (x : KS) : KS :=
  let y := (s.t r).foldl (tStep eσ w) (0, 0, x.2.2)
  (x.1 + mulNZ w y.1, x.2.1 + mulNZ w y.2.1, y.2.2)

theorem foldl_tStep (eσ : ℕ → F) (w : F) : ∀ (l : LinT) (x : KS),
    l.foldl (tStep eσ w) x =
      (l.foldl (fun a t => a + match t.1 with | .loc k => cmulF t.2 (eσ k) | _ => 0) x.1,
       l.foldl (fun a t => a + match t.1 with | .one => t.2 | _ => 0) x.2.1, l.foldl (uStep w) x.2.2)
  | [], _ => rfl
  | t :: l, x => by
    rw [List.foldl_cons, foldl_tStep eσ w l, List.foldl_cons, List.foldl_cons, List.foldl_cons]
    obtain ⟨wi, c⟩ := t
    cases wi <;> simp [tStep, uStep]

theorem kp1_eq (s : Mat) (eσ : ℕ → F) (w : F) (r : RowT) (x : KS) :
    kp1 s eσ w r x = (x.1 + mulNZ w (locRow eσ (s.t r)), x.2.1 + mulNZ w (oneRow (s.t r)),
      (s.t r).foldl (uStep w) x.2.2) := by
  simp only [kp1, foldl_tStep, locRow, oneRow, sumL]

/-- The rows from index `i`, once, for the three matrices. -/
def kpGo (eτ eσ : ℕ → F) : ℕ → List RowT → KS × KS × KS → KS × KS × KS
  | _, [], st => st
  | i, r :: rs, st =>
    let w := eτ i
    kpGo eτ eσ (i + 1) rs (kp1 .a eσ w r st.1, kp1 .b eσ w r st.2.1, kp1 .c eσ w r st.2.2)

/-- The number of inputs matrix `s` reads (`inpN` without the index). -/
def inpNF (s : Mat) (T : List RowT) : ℕ := T.foldl (fun m r => (s.t r).foldl inpStep m) 0

/-- **A key's three preparations in one pass over its rows** (`kprep3F_eq`). -/
def kprep3F (eτ eσ : ℕ → F) (K : Key) : KP × KP × KP :=
  let st := kpGo eτ eσ 0 K.rows ((0, 0, Array.replicate (inpNF .a K.rows) 0),
    (0, 0, Array.replicate (inpNF .b K.rows) 0), (0, 0, Array.replicate (inpNF .c K.rows) 0))
  (⟨st.1.1, st.1.2.1, st.1.2.2⟩, ⟨st.2.1.1, st.2.1.2.1, st.2.1.2.2⟩,
    ⟨st.2.2.1, st.2.2.2.1, st.2.2.2.2⟩)

/-- One matrix's part of the pass: its three folds over the indexed rows. -/
def kOne (s : Mat) (eτ eσ : ℕ → F) (n : ℕ) (rs : List RowT) (x : KS) : KS :=
  ((rs.zipIdx n).foldl (fun a p => a + mulNZ (eτ p.2) (locRow eσ (s.t p.1))) x.1,
   (rs.zipIdx n).foldl (fun a p => a + mulNZ (eτ p.2) (oneRow (s.t p.1))) x.2.1,
   (rs.zipIdx n).foldl (fun U p => (s.t p.1).foldl (uStep (eτ p.2)) U) x.2.2)

theorem kpGo_eq (eτ eσ : ℕ → F) : ∀ (rs : List RowT) (n : ℕ) (st : KS × KS × KS),
    kpGo eτ eσ n rs st = (kOne .a eτ eσ n rs st.1, kOne .b eτ eσ n rs st.2.1, kOne .c eτ eσ n rs st.2.2)
  | [], _, _ => rfl
  | r :: rs, n, st => by
    rw [kpGo, kpGo_eq eτ eσ rs (n + 1)]
    simp only [kOne, kp1_eq, List.zipIdx_cons, List.foldl_cons]

theorem foldl_zipIdx_fst {α β : Type*} (g : β → α → β) : ∀ (T : List α) (n : ℕ) (m : β),
    (T.zipIdx n).foldl (fun m p => g m p.1) m = T.foldl g m
  | [], _, _ => rfl
  | a :: T, n, m => by rw [List.zipIdx_cons, List.foldl_cons, List.foldl_cons, foldl_zipIdx_fst g T]

theorem inpNF_eq (s : Mat) (T : List RowT) : inpNF s T = inpN s T :=
  (foldl_zipIdx_fst (fun m r => (s.t r).foldl inpStep m) T 0 0).symm

/-- **The one pass is the three preparations.** -/
theorem kprep3F_eq (eτ eσ : ℕ → F) (K : Key) :
    kprep3F eτ eσ K = (kprepF .a eτ eσ K, kprepF .b eτ eσ K, kprepF .c eτ eσ K) := by
  simp only [kprep3F, kpGo_eq, kOne, kprepF, sumL, inpU, inpNF_eq]

/-! ## The keys' `eq` tables, once per evaluation -/

/-- `eq(t_{<A}, ·)` for every `A` with `need[A]` (the others empty). -/
def preTabs (t : ℕ → F) (need : Array Bool) : Array (Array F) :=
  (Array.range need.size).map fun A => if need.getD A false then loTab A t else #[]

/-- The table of `A` bits: from `preTabs` when built, else computed. -/
def tabOr (P : Array (Array F)) (need : Array Bool) (t : ℕ → F) (A : ℕ) : Array F :=
  if need.getD A false then P.getD A #[] else loTab A t

theorem getD_true {need : Array Bool} {A : ℕ} (h : need.getD A false = true) : A < need.size := by
  by_contra h'
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem tabOr_eq (t : ℕ → F) (need : Array Bool) (A : ℕ) : tabOr (preTabs t need) need t A = loTab A t := by
  unfold tabOr; split_ifs with h
  · have h3 : need[A]'(getD_true h) = true := by
      simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (getD_true h)] using h
    simp [preTabs, Array.getD_eq_getD_getElem?, getD_true h, h3]
  · rfl

/-- The bits `< m` that some key has as `A` (resp. `B`), or `B` of a pattern in `pats`. -/
def needAll (keys : Array Key) (f : Key → ℕ) (m : ℕ) (extra : List ℕ := []) : Array Bool :=
  (Array.range m).map fun A => keys.any (f · == A) || extra.contains A

/-! ## Runs -/

/-- **A run pattern**: own inputs `j0 … j0 + len − 1` read the cells `2^B·ch + r + t`. -/
structure Pat where
  j0 : ℕ
  r : ℕ
  len : ℕ
  B : ℕ
  deriving BEq, Hashable

/-- The empty pattern (a lookup's default; never valid). -/
def dpat : Pat := ⟨0, 0, 0, 0⟩

/-- A valid pattern: a nonempty run inside one aligned chunk of at most `2^12` cells. -/
def Pat.ok (p : Pat) : Prop := 1 ≤ p.len ∧ p.B ≤ 12 ∧ p.r + p.len ≤ 2 ^ p.B

/-- A prepared own input: a grouped form, or a run (pattern index, chunk). -/
inductive OwnP where
  | g (f : GForm)
  | run (i ch : ℕ)

/-- The one-cell forms of the cells `c, c + 1, …`. -/
def cellsFrom (c len : ℕ) : List Lin := (List.range len).map fun t => [(c + t, 1)]

/-- **The run check**: the forms `ls` (own input `j` on) start with pattern `p`'s run; its chunk. -/
def runCh (p : Pat) (j : ℕ) (ls : List Lin) : Option ℕ :=
  match ls with
  | [(c, _)] :: _ =>
    if p.j0 == j && decide (1 ≤ p.len) && decide (p.B ≤ 12) && decide (p.r + p.len ≤ 2 ^ p.B) &&
      c % 2 ^ p.B == p.r && eqL (ls.take p.len) (cellsFrom c p.len) then some (c / 2 ^ p.B) else none
  | _ => none

theorem runCh_spec {p : Pat} {j : ℕ} {ls : List Lin} {ch : ℕ} (h : runCh p j ls = some ch) :
    p.j0 = j ∧ p.ok ∧ ls = cellsFrom (2 ^ p.B * ch + p.r) p.len ++ ls.drop p.len := by
  unfold runCh at h
  split at h
  · rename_i c u rest
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    refine ⟨h1, ⟨h2, h3, h4⟩, ?_⟩
    have hc' : 2 ^ p.B * (c / 2 ^ p.B) + p.r = c := by rw [← h5]; exact Nat.div_add_mod c _
    rw [hc', ← eqL_eq h6, List.take_append_drop]
  · cases h

/-- The first pattern of `ix` whose run starts here. -/
def findRun (ps : Array Pat) (j : ℕ) (ls : List Lin) : List ℕ → Option (ℕ × ℕ)
  | [] => none
  | i :: is => match runCh (ps.getD i dpat) j ls with
    | some ch => some (i, ch)
    | none => findRun ps j ls is

theorem findRun_spec {ps : Array Pat} {j : ℕ} {ls : List Lin} :
    ∀ {ix : List ℕ} {i ch : ℕ}, findRun ps j ls ix = some (i, ch) → runCh (ps.getD i dpat) j ls = some ch
  | [], _, _, h => by cases h
  | i' :: is, i, ch, h => by
    unfold findRun at h
    split at h
    · rename_i ch' hc; cases h; exact hc
    · exact findRun_spec h

theorem findRun_len {ps : Array Pat} {j : ℕ} {ls : List Lin} {ix : List ℕ} {i ch : ℕ}
    (h : findRun ps j ls ix = some (i, ch)) : 1 ≤ (ps.getD i dpat).len :=
  (runCh_spec (findRun_spec h)).2.1.1

/-- **An instance's own forms, prepared** (own input `j` on): a run where a pattern of `ps` (tried
in the order `ix`) checks, else the grouped form. -/
def prepOwn (ps : Array Pat) (ix : List ℕ) (j : ℕ) (ls : List Lin) : List OwnP :=
  match ls with
  | [] => []
  | l :: rest =>
    match h : findRun ps j (l :: rest) ix with
    | some (i, ch) =>
      .run i ch :: prepOwn ps ix (j + (ps.getD i dpat).len) ((l :: rest).drop (ps.getD i dpat).len)
    | none => .g (grp 4096 l) :: prepOwn ps ix (j + 1) rest
termination_by ls.length
decreasing_by
  · have := findRun_len h; simp only [List.length_drop, List.length_cons]; omega
  · simp

/-- **The own inputs' value** with runs: `inr[i]` is pattern `i`'s inner sum, `hf B ch` the high
factor `eq(σ_{≥B}, ch)`. -/
def ownSumP (U slo shi inr : Array F) (hf : ℕ → ℕ → F) (ps : Array Pat) : ℕ → List OwnP → F
  | _, [] => 0
  | j, .g f :: os => U.getD j 0 * glVal slo shi f + ownSumP U slo shi inr hf ps (j + 1) os
  | j, .run i ch :: os => hf (ps.getD i dpat).B ch * inr.getD i 0 +
      ownSumP U slo shi inr hf ps (j + (ps.getD i dpat).len) os

/-- **A pattern's inner sum** `Σ_t U[j + j0 + t] · lt[r + t]` (`j`: the key's shared inputs). -/
def runIn (U lt : Array F) (j : ℕ) (p : Pat) : F :=
  sumL (fun t => U.getD (j + p.j0 + t) 0 * lt.getD (p.r + t) 0) (List.range p.len)

/-- The inner sums of a key's patterns. -/
def inrOf (U : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) : Array F :=
  ps.map fun p => runIn U (lt p.B) j p

theorem inrOf_getD {U : Array F} {lt : ℕ → Array F} {j : ℕ} {ps : Array Pat} {i : ℕ}
    (h : (ps.getD i dpat).ok) :
    (inrOf U lt j ps).getD i 0 = runIn U (lt (ps.getD i dpat).B) j (ps.getD i dpat) := by
  have hi : i < ps.size := by
    by_contra h'
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
    exact absurd h.1 (by simp [dpat])
  simp [inrOf, Array.getD_eq_getD_getElem?, hi]

theorem ownSum_append (U slo shi : Array F) :
    ∀ (a b : List GForm) (j : ℕ), ownSum U slo shi j (a ++ b) =
      ownSum U slo shi j a + ownSum U slo shi (j + a.length) b
  | [], b, j => by simp [ownSum]
  | x :: a, b, j => by
    rw [List.cons_append, ownSum, ownSum, ownSum_append U slo shi a b (j + 1), List.length_cons]
    rw [show j + 1 + a.length = j + (a.length + 1) by omega, add_assoc]

/-- **A run's value**: `Σ_t U[j + t] · E(cell (2^B·ch + r + t)) = eq(σ_{≥B}, ch) · runIn`. -/
theorem run_val (U slo shi : Array F) (u : ℕ → F)
    (hE : ∀ l, glVal slo shi (grp 4096 l) = linE (RingHom.id F) 23 u l) (p : Pat) (hp : p.ok)
    (j ch : ℕ) :
    ownSum U slo shi (j + p.j0) ((cellsFrom (2 ^ p.B * ch + p.r) p.len).map (grp 4096)) =
      gN (23 - p.B) (fun l => u (p.B + l)) ch * runIn U (loTab p.B u) j p := by
  obtain ⟨_, hB, hr⟩ := hp
  rw [ownSum_eq U slo shi _ hE, runIn, sumL_eq, ← List.sum_map_mul_left, cellsFrom, List.length_map,
    List.length_range]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have ht' := List.mem_range.1 ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht', Option.map_some,
    Option.getD_some, loTab_getD _ _ (by omega)]
  simp only [linE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_one, one_mul]
  rw [show 2 ^ p.B * ch + p.r + t = 2 ^ p.B * ch + (p.r + t) by omega,
    gN_split (by omega) _ _ (by omega)]
  ring

/-- **`ownSumP` of the prepared forms is `ownSum` of the forms**, for any pattern table (`j0`: the
key's shared inputs; `inr` the patterns' inner sums, `hf` the high factor). -/
theorem ownSumP_eq (U slo shi inr : Array F) (hf : ℕ → ℕ → F) (ps : Array Pat) (ix : List ℕ)
    (u : ℕ → F) (j0 : ℕ) (hE : ∀ l, glVal slo shi (grp 4096 l) = linE (RingHom.id F) 23 u l)
    (hhf : ∀ B ch, B ≤ 12 → hf B ch = gN (23 - B) (fun l => u (B + l)) ch)
    (hin : ∀ i, (ps.getD i dpat).ok →
      inr.getD i 0 = runIn U (loTab (ps.getD i dpat).B u) j0 (ps.getD i dpat)) :
    ∀ (n : ℕ) (own : List Lin), own.length = n → ∀ j : ℕ,
      ownSumP U slo shi inr hf ps (j0 + j) (prepOwn ps ix j own) =
        ownSum U slo shi (j0 + j) (own.map (grp 4096)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro own hn j
    match own with
    | [] => rw [prepOwn]; rfl
    | l :: rest =>
      rw [prepOwn]
      split
      · rename_i i ch h
        obtain ⟨hj, hok, hls⟩ := runCh_spec (findRun_spec h)
        have hlen := findRun_len h
        set p := ps.getD i dpat
        have hm : (l :: rest).map (grp 4096) = (cellsFrom (2 ^ p.B * ch + p.r) p.len).map (grp 4096) ++
            ((l :: rest).drop p.len).map (grp 4096) := by
          conv_lhs => rw [hls]
          rw [List.map_append]
        rw [ownSumP, hm, ownSum_append, List.length_map, cellsFrom, List.length_map, List.length_range,
          ← cellsFrom, add_assoc, ih _ (by simp only [List.length_drop, List.length_cons] at hn ⊢; omega) _ rfl,
          ← hj, run_val U slo shi u hE p hok j0 ch, hhf _ _ hok.2.1, hin i hok]
      · rw [ownSumP, List.map_cons, ownSum, add_assoc,
          ih _ (by simp only [List.length_cons] at hn; omega) _ rfl]

/-! ## The three matrices -/

/-- The own inputs of the three matrices, with runs. -/
def ownSumP3 (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ℕ → List OwnP → F3
  | _, [] => (0, 0, 0)
  | j, .g f :: os =>
    let e := glVal slo shi f
    add3 (Ua.getD j 0 * e, Ub.getD j 0 * e, Uc.getD j 0 * e) (ownSumP3 Ua Ub Uc slo shi inr hf ps (j + 1) os)
  | j, .run i ch :: os =>
    let p := ps.getD i dpat
    let h := hf p.B ch
    let v := inr.getD i (0, 0, 0)
    add3 (h * v.1, h * v.2.1, h * v.2.2) (ownSumP3 Ua Ub Uc slo shi inr hf ps (j + p.len) os)

theorem getD_map3 (inr : Array F3) (f : F3 → F) (hf : f (0, 0, 0) = 0) (i : ℕ) :
    (inr.map f).getD i 0 = f (inr.getD i (0, 0, 0)) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases inr[i]? <;> simp [hf]

theorem ownSumP3_eq (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ∀ (j : ℕ) (os : List OwnP), ownSumP3 Ua Ub Uc slo shi inr hf ps j os =
      (ownSumP Ua slo shi (inr.map (·.1)) hf ps j os, ownSumP Ub slo shi (inr.map (·.2.1)) hf ps j os,
        ownSumP Uc slo shi (inr.map (·.2.2)) hf ps j os)
  | _, [] => rfl
  | j, .g f :: os => by rw [ownSumP3, ownSumP3_eq Ua Ub Uc slo shi inr hf ps (j + 1) os]; rfl
  | j, .run i ch :: os => by
    rw [ownSumP3, ownSumP3_eq Ua Ub Uc slo shi inr hf ps _ os]
    simp only [ownSumP, add3, getD_map3 inr (·.1) rfl, getD_map3 inr (·.2.1) rfl,
      getD_map3 inr (·.2.2) rfl]

/-- The three inner sums of a pattern (one table lookup each). -/
def runIn3 (Ua Ub Uc lt : Array F) (j : ℕ) (p : Pat) : F3 :=
  sum3 (fun t => let e := lt.getD (p.r + t) 0; let q := j + p.j0 + t
    (Ua.getD q 0 * e, Ub.getD q 0 * e, Uc.getD q 0 * e)) (List.range p.len)

def inrOf3 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) : Array F3 :=
  ps.map fun p => runIn3 Ua Ub Uc (lt p.B) j p

theorem inrOf3_map1 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.1) = inrOf Ua lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem inrOf3_map2 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.2.1) = inrOf Ub lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem inrOf3_map3 (Ua Ub Uc : Array F) (lt : ℕ → Array F) (j : ℕ) (ps : Array Pat) :
    (inrOf3 Ua Ub Uc lt j ps).map (·.2.2) = inrOf Uc lt j ps := by
  simp [inrOf3, inrOf, Function.comp_def, runIn3, sum3_eq, runIn]

theorem range_getD_inr (pats : Array (Array Pat)) (U : ℕ → Array F) (lt : ℕ → Array F) (J : ℕ → ℕ)
    (k : ℕ) : ((Array.range pats.size).map fun k => inrOf (U k) lt (J k) (pats.getD k #[])).getD k #[] =
      inrOf (U k) lt (J k) (pats.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]; simp [inrOf]

theorem range_getD_inr3 (pats : Array (Array Pat)) (Ua Ub Uc : ℕ → Array F) (lt : ℕ → Array F)
    (J : ℕ → ℕ) (k : ℕ) :
    ((Array.range pats.size).map fun k => inrOf3 (Ua k) (Ub k) (Uc k) lt (J k) (pats.getD k #[])).getD k #[] =
      inrOf3 (Ua k) (Ub k) (Uc k) lt (J k) (pats.getD k #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs with h
  · rfl
  · rw [Array.getElem?_eq_none (by omega)]; simp [inrOf3]

/-! ## The search for patterns (untrusted: `prepOwn` checks every run) -/

/-- The runs of one instance's own forms at chunk bits `B`: maximal runs of consecutive one-cell
forms (coefficient `1`) inside one aligned chunk, of length at least 2. -/
def runsOf (B : ℕ) (own : List Lin) : List Pat :=
  let W := 2 ^ B
  let fl := fun (cur : Option (ℕ × ℕ × ℕ)) (acc : List Pat) => match cur with
    | some (j0, c0, len) => if 2 ≤ len then (⟨j0, c0 % W, len, B⟩ : Pat) :: acc else acc
    | none => acc
  let r := own.foldl (fun (q : ℕ × Option (ℕ × ℕ × ℕ) × List Pat) l =>
    match l with
    | [(c, u)] =>
      if u == 1 then
        match q.2.1 with
        | some (j0, c0, len) =>
          if c == c0 + len && c % W != 0 then (q.1 + 1, some (j0, c0, len + 1), q.2.2)
          else (q.1 + 1, some (q.1, c, 1), fl q.2.1 q.2.2)
        | none => (q.1 + 1, some (q.1, c, 1), q.2.2)
      else (q.1 + 1, none, fl q.2.1 q.2.2)
    | _ => (q.1 + 1, none, fl q.2.1 q.2.2)) (0, none, [])
  (fl r.2.1 r.2.2).reverse

/-- The distinct values of a list, in order. -/
def dedupP (l : List Pat) : List Pat :=
  (l.foldl (fun (q : Std.HashSet Pat × List Pat) p =>
    if q.1.contains p then q else (q.1.insert p, p :: q.2)) ({}, [])).2.reverse

/-- **A key's patterns**: the chunk bits `B ∈ [2, 9]` of least estimated cost (4 products per run
and per own input outside a run, 6 per pattern entry: three matrices, two slots), or none. -/
def patsFor (insts : List (List Lin)) : Array Pat :=
  let own := insts.foldl (fun n o => n + o.length) 0
  let best := [2, 3, 4, 5, 6, 7, 8, 9].foldl (fun (q : ℕ × List Pat) B =>
    let rs := insts.map (runsOf B)
    let nr := rs.foldl (fun n l => n + l.length) 0
    let cov := rs.foldl (fun n l => n + l.foldl (fun m p => m + p.len) 0) 0
    let ds := dedupP rs.flatten
    let cost := 4 * nr + 4 * (own - cov) + 6 * ds.foldl (fun m p => m + p.len) 0
    if cost < q.1 then (cost, ds) else q) (4 * own, [])
  best.2.toArray

/-- **The plan's pattern tables**, per key, from the instances of both slots. -/
def mkPats (nk : ℕ) (pcs : List Piece) : Array (Array Pat) :=
  let insts := pcs.foldl (fun (a : Array (List (List Lin))) p => match p with
    | .ins k _ _ own => if k < a.size then a.modify k (own :: ·) else a
    | .sp _ => a) (Array.replicate nk [])
  insts.map patsFor

/-! ## Controls -/

/-- (+) A run of three cells at offset 1 of a 4-cell chunk is found. -/
theorem runCh_pos : runCh ⟨0, 1, 3, 2⟩ 0 [[(9, 1)], [(10, 1)], [(11, 1)]] = some 2 := by
  simp [runCh, cellsFrom, eqL, List.range_succ]

/-- (−) A run that crosses its chunk is refused (cells 10, 11, 12 at `B = 2`: `1 + 3 > 4`). -/
theorem runCh_cross : runCh ⟨0, 2, 3, 2⟩ 0 [[(10, 1)], [(11, 1)], [(12, 1)]] = none := by
  simp [runCh]

/-- (−) A gap in the cells is refused. -/
theorem runCh_gap : runCh ⟨0, 1, 3, 2⟩ 0 [[(9, 1)], [(10, 1)], [(12, 1)]] = none := by
  simp [runCh, cellsFrom, eqL, List.range_succ]

end TEval
end FR
