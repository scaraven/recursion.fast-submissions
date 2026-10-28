-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4; stage R4c).
import FRSoundness4R4At

/-!
# The outs of earlier phases come before `next` (`gen4`)

3.x's `genPhase_out_lt`/`skeleton_out_lt` (`FRSoundnessAccLvl`) for `genPhase4`:

* **`genPhase4_out_lt`**: a phase's out registers are below the next free register (a rounds
  phase's first claim may be the context's `uni` register, hence the hypothesis);
* **`cAt4_succ`**, **`cAt4_next_mono`**: the generator's contexts phase by phase;
* **`cAt4_outs_lt`**: on an accepted run, every register of an earlier phase's outs is below the
  context's `next` (`OutsLt`); so **`segPt_lt`**: the segment's `segPtRegs` precede Z2 (`uni_view4`'s
  `hpt`), and **`skeleton4_out_lt`**: every register the skeleton exports is one of its registers.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (S : Seq) (p : KindP)

theorem opsOut_absorbOps (f o len st b : ℕ) : opsOut (absorbOps f o len st b) = 2 := rfl
theorem opsOut_flatMap (g : ℕ → List Op) (w : ℕ) (hg : ∀ k, opsOut (g k) = w) :
    ∀ l : List ℕ, opsOut (l.flatMap g) = w * l.length
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, opsOut_append, hg, opsOut_flatMap g w hg l]; simp; ring

theorem opsOut_lastOps (o b : ℕ) : opsOut (lastOps o b) = 94 := by
  simp only [lastOps, opsOut_append]
  rw [opsOut_flatMap _ 2 (fun _ => rfl), opsOut_flatMap _ 3 (fun _ => rfl)]; rfl
theorem opsOut_seedOps4 (b : ℕ) : opsOut (seedOps4 p b) = 4 := rfl

theorem opsOut_nil : opsOut [] = 0 := rfl

theorem opsOut_cons (op : Op) (l : List Op) : opsOut (op :: l) = op.outs + opsOut l := by
  simp [opsOut]

theorem opsOut_sqzCoordOps : ∀ k st b, opsOut (sqzCoordOps k st b) = 3 * k
  | 0, _, _ => rfl
  | k + 1, st, b => by
    rw [sqzCoordOps, opsOut_append, opsOut_sqzCoordOps k]; show 3 + 3 * k = _; ring

theorem opsOut_sqzOps : ∀ k st b, opsOut (sqzOps k st b) = k
  | 0, _, _ => rfl
  | k + 1, st, b => by rw [sqzOps, opsOut_cons, opsOut_sqzOps k]; simp [Op.outs]; ring

theorem opsOut_uniOps (f o st pt b : ℕ) : opsOut (uniOps f o st pt b) = 136 := by
  simp only [uniOps, opsOut_append]
  have : opsOut (uniElems f o) = 127 := by simp [uniElems, opsOut, Function.comp_def, Op.outs]
  rw [this]; rfl

theorem opsOut_roundOpsF (f o deg : ℕ) (real : KC Bool) (st claim b : ℕ) :
    opsOut (roundOpsF f o deg real st claim b) = roundW deg := by
  unfold roundOpsF roundW
  split_ifs <;> simp only [opsOut_append, opsOut_cons, Op.outs, opsOut_nil]

theorem opsOut_roundOpsK (f o : ℕ) (real : KC Bool) (st claim b : ℕ) :
    opsOut (roundOpsK f o real st claim b) = 13 := rfl

theorem opsOut_roundsOps (f o deg : ℕ) (inK : Bool) (real : KC ℕ) :
    ∀ n j st claim b, opsOut (roundsOps f o deg inK real n j st claim b) =
      (if inK then 13 else roundW deg) * n
  | 0, _, _, _, _ => by simp [roundsOps, opsOut]
  | n + 1, j, st, claim, b => by
    simp only [roundsOps, opsOut_append, opsOut_roundsOps f o deg inK real n]
    cases inK <;> simp only [Bool.false_eq_true, ite_false, ite_true, opsOut_roundOpsF,
      opsOut_roundOpsK] <;> ring

theorem opsOut_merkleOps4 (sib i : ℕ) (j : Reg) : ∀ n h cur so b, opsOut (merkleOps4 sib i j n h cur so b) = 6 * n
  | 0, _, _, _, _ => rfl
  | n + 1, h, cur, so, b => by
    rw [merkleOps4, opsOut_append, opsOut_merkleOps4 sib i j n]; simp [opsOut, Op.outs]; try ring

theorem opsOut_posOps4 (k : KindP) (i co so capO : ℕ) (ans : List Reg) (w : Reg) (q b : ℕ) :
    opsOut (posOps4 S k i co so capO ans w q b) = posW4 S i := by
  simp only [posOps4, opsOut_append, opsOut_merkleOps4]; simp [opsOut, Op.outs, posW4]; try ring

/-- **A phase's out registers are below the next free register.** -/
theorem genPhase4_out_lt (n : ℕ) (ph : String × Sh) (c : GCtx) (hu : ph.2 = .seed ∨ c.uni < c.next) :
    ∀ x ∈ (genPhase4 S p n ph c).2.outs.back?.getD [], x < (genPhase4 S p n ph c).2.next := by
  obtain ⟨name, sh⟩ := ph
  simp only [Reg]
  cases sh with
  | seed => simp only [genPhase4, opsOut_seedOps4]; simp
  | absorb f len =>
    simp only [genPhase4]
    split_ifs <;>
    simp only [Array.back?_push, Option.getD_some, List.mem_cons, List.mem_singleton, lastOuts,
      List.mem_map, List.mem_range, opsOut_append, opsOut_absorbOps, opsOut_lastOps,
      List.not_mem_nil, or_false] <;>
    (try rintro x (rfl | rfl | ⟨k, hk, rfl⟩)) <;> (try rintro x rfl) <;> omega
  | squeezes k ch =>
    cases ch with
    | coords =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_cons, List.mem_map,
        List.mem_range, opsOut_append, opsOut_sqzCoordOps]
      rintro x (rfl | ⟨y, hy, rfl⟩)
      · simp [opsOut, Op.outs]
      · simp only [opsOut, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Op.outs]; omega
    | one =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_singleton, opsOut_append,
        opsOut_sqzOps]
      rintro x rfl; simp [opsOut, Op.outs]
    | pos i =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_map, List.mem_range,
        opsOut_sqzOps]
      rintro x ⟨y, hy, rfl⟩; omega
  | uni f =>
    simp only [genPhase4]
    split_ifs <;>
    simp only [Array.back?_push, Option.getD_some, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, opsOut_cons, opsOut_uniOps] <;>
    rintro x (rfl | rfl | rfl) <;> simp [Op.outs]
  | rounds f k deg inK =>
    have hu' : c.uni < c.next := by simpa using hu
    have hR : 4 ≤ roundW deg := by unfold roundW; split <;> omega
    have key : ∀ w, 4 ≤ w → ∀ (cl b' : ℕ), cl < b' → ∀ x ∈ cl ::
        ((List.range k).map (fun j => b' + w * j + 3) ++ [if k = 0 then cl else b' + w * k - 1]),
        x < b' + w * k := by
      intro w hw cl b' hcl x hx
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩ | rfl
      · rcases Nat.eq_zero_or_pos k with rfl | hk <;> nlinarith
      · nlinarith
      · split <;> omega
    rcases hi : initClaim name with _ | _ | _ <;> cases inK <;>
    simp only [genPhase4, hi, initOps, Init.width, Array.back?_push, Option.getD_some, opsOut_append,
      opsOut_roundsOps, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte] <;>
    intro x hx
    · have := key _ hR c.uni (c.next + 0) (by omega) x hx; simp only [opsOut] at *; omega
    · have := key 13 (by omega) c.uni (c.next + 0) (by omega) x hx; simp only [opsOut] at *; omega
    · have := key _ hR c.next (c.next + 1) (by omega) x hx; simp [opsOut, Op.outs] at *; omega
    · have := key 13 (by omega) c.next (c.next + 1) (by omega) x hx; simp [opsOut, Op.outs] at *; omega
    · have := key _ hR (c.next + 2) (c.next + 3) (by omega) x hx; simp [opsOut, Op.outs] at *; omega
    · have := key 13 (by omega) (c.next + 2) (c.next + 3) (by omega) x hx
      simp [opsOut, Op.outs] at *; omega
  | queries i =>
    simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_map, List.mem_range,
      opsOut_cons, opsOut_flatMap _ _ (fun q => opsOut_posOps4 S _ _ _ _ _ _ _ _ _)]
    have : 4 ≤ posW4 S i := by unfold posW4; omega
    rintro x ⟨q, hq, rfl⟩
    rw [opsOut_append, opsOut_flatMap _ (posW4 S i) (fun q => opsOut_posOps4 S _ _ _ _ _ _ _ _ _),
      List.length_range]
    have h2 : opsOut [Op.packK c.foldR, Op.eqTableK c.next] = 2 := rfl
    rw [h2]
    nlinarith

/-! ## The generator's contexts -/

theorem genPhases4_split : ∀ (A B : List (String × Sh)) (n : ℕ) (c : GCtx),
    (genPhases4 S p (A ++ B) n c).2 = (genPhases4 S p B (n + A.length) (genPhases4 S p A n c).2).2
  | [], B, n, c => by simp [genPhases4]
  | ph :: A, B, n, c => by
    simp only [List.cons_append, genPhases4]
    rw [genPhases4_split A B (n + 1)]
    simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem cAt4_succ {k : ℕ} (hk : k < (phasesOf S).length) :
    cAt4 S p (k + 1) = (genPhase4 S p k (phasesOf S)[k] (cAt4 S p k)).2 := by
  rw [cAt4, List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, genPhases4_split,
    List.length_take, min_eq_left hk.le, Nat.zero_add]
  rfl

theorem cAt4_next_succ {k : ℕ} (hk : k < (phasesOf S).length) :
    (cAt4 S p k).next ≤ (cAt4 S p (k + 1)).next := by
  rw [cAt4_succ S p hk, (genPhase4_next S p k _ _).1]; omega

theorem cAt4_next_mono {m : ℕ} : ∀ {k : ℕ}, m ≤ k → k ≤ (phasesOf S).length →
    (cAt4 S p m).next ≤ (cAt4 S p k).next
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | k + 1, h, hk => by
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · exact (cAt4_next_mono (by omega) (by omega)).trans (cAt4_next_succ S p (by omega))
    · rw [show m = k + 1 by omega]

theorem cAt4_size (k : ℕ) : (cAt4 S p k).outs.size = min k (phasesOf S).length := by
  have := (genPhases4_outs S p ((phasesOf S).take k) 0 ctx0).1
  simpa [cAt4, ctx0] using this

theorem skeleton4_eq_cAt4 : (skeleton4 S p).2 = cAt4 S p (phasesOf S).length := by
  rw [cAt4, List.take_length]; rfl

/-- **An earlier phase's outs in a context are the skeleton's.** -/
theorem cAt4_outs {m n : ℕ} (hmn : m < n) (hn : n ≤ (phasesOf S).length) :
    (cAt4 S p n).outs.getD m [] = (skeleton4 S p).2.outs.getD m [] := by
  have e : (skeleton4 S p).2 = (genPhases4 S p ((phasesOf S).drop n) (0 + n) (cAt4 S p n)).2 := by
    have := genPhases4_split S p ((phasesOf S).take n) ((phasesOf S).drop n) 0 ctx0
    rw [List.take_append_drop, List.length_take, min_eq_left hn] at this
    exact this
  rw [e, genPhases4_prefix S p _ _ _ m (by rw [cAt4_size, min_eq_left hn]; exact hmn)]

/-! ## Outs before `next` -/

/-- Every register of the context's outs is below its `next`. -/
def OutsLt (c : GCtx) : Prop := ∀ m, ∀ x ∈ c.outs.getD m [], x < c.next

theorem genPhase4_outsLt (n : ℕ) (ph : String × Sh) (c : GCtx) (hc : OutsLt c)
    (hu : ph.2 = .seed ∨ c.uni < c.next) : OutsLt (genPhase4 S p n ph c).2 := by
  intro m x hx
  have hlt := genPhase4_out_lt S p n ph c hu
  have hnx := (genPhase4_next S p n ph c).1
  rw [genPhase4_outs] at hx
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at hx
  split_ifs at hx
  · exact hlt x (by simpa using hx)
  · have := hc m x (by simpa [Array.getD_eq_getD_getElem?] using hx)
    exact lt_of_lt_of_le this (by rw [hnx]; exact Nat.le_add_right _ _)

/-- **On an accepted run, every context's outs precede its `next`.** -/
theorem cAt4_outsLt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) :
    ∀ k ≤ (phasesOf seq4).length, OutsLt (cAt4 seq4 p k)
  | 0, _ => fun m x hx => by simp [cAt4, genPhases4, ctx0, Array.getD_eq_getD_getElem?] at hx
  | k + 1, hk => by
    rw [cAt4_succ seq4 p (by omega)]
    obtain ⟨trk, M, x', hx', hb, hwf, -⟩ := phase_at4 impl κ inp p h (k := k) (by omega)
    refine genPhase4_outsLt seq4 p k _ _ (cAt4_outsLt h k (by omega)) ?_
    rcases hwf with ⟨h', -⟩ | h'
    · exact .inl h'
    · right; have := h'.2.1; simpa [hb] using this

/-- **The segment's `targetS` operand's registers precede Z2** (`uni_view4`'s `hpt`). -/
theorem segPt_lt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) {n : ℕ}
    (h3 : 3 < n) (hn : n ≤ (phasesOf seq4).length) :
    ∀ x ∈ segPtRegs seq4 p (cAt4 seq4 p n).outs, x < (cAt4 seq4 p n).next := by
  have hO := cAt4_outsLt p h n hn
  have hpos : 0 < (cAt4 seq4 p n).next :=
    lt_of_lt_of_le (by rw [(cAt4_ctl seq4 p).2.1]; omega) (cAt4_next_mono seq4 p (m := 1) (by omega) hn)
  intro x hx
  simp only [segPtRegs, List.mem_append, List.mem_replicate] at hx
  rcases hx with (hx | ⟨-, rfl⟩) | hx
  · exact hO 3 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · rw [List.getD_eq_getElem?_getD]
    rcases hq : ((cAt4 seq4 p n).outs.getD 1 [])[1]? with _ | z
    · exact hpos
    · exact hO 1 z (List.mem_of_getElem? hq)
  · exact hO 1 x (List.mem_of_mem_drop hx)

/-- **Every register the skeleton exports is one of its registers.** -/
theorem skeleton4_out_lt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) :
    ∀ m, ∀ x ∈ (skeleton4 seq4 p).2.outs.getD m [], x < (#[] ++ y.1.toArray).size := by
  intro m x hx
  rw [← skeleton4_next impl κ inp seq4 p h]
  rw [skeleton4_eq_cAt4] at hx ⊢
  exact cAt4_outsLt p h _ le_rfl m x hx

end FR.Snd.R4
