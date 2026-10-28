-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh`; stage R4b, for P4c's F2).
import FRVerifierC4

/-!
# A segment's `finSh` has no link weight

`gShCore` runs `linkWAll`/`linkOps` for every kind. On the segment program the kind index is
`(KindP.ofSeg σ).tix = .L32`, not a node, so the concrete implementation (`implSeg (implC …)`) and
its specification (`specSeg (specC …)`) both answer `0^8` (`linkWAll_segC`, `linkWAll_segS`; any
implementation meeting the specification does, `linkWAll_seg_of_meets`). Then:

* **`linkSum_zero`**: `relSh`'s link term `linkSum 0^8 κ_s n acc pow` is `acc`;
* **`run_linkOps_zero`** (the program): with `0^8` in `linkWAll`'s register `b + 25`, `linkOps ks b`
  passes and its accumulator register `b + 57` holds register `b + 22`'s value: the 32 link ops add
  nothing to `finSh` (ii)'s weight. So P4c's `wSumSeg` (no link term) is the program's value.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- The link families' sum over `0^8` is the accumulator. -/
theorem linkSum_zero (ks : F) : ∀ (n : ℕ) (acc pow : F),
    linkSum (Array.replicate nLinkFam 0) ks n acc pow = acc
  | 0, _, _ => rfl
  | n + 1, acc, pow => by
    rw [linkSum, linkSum_zero ks n, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split_ifs <;> simp

/-- The segment's concrete `linkWAll` is `0^8`. -/
theorem linkWAll_segC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) (tt rr : Array F) :
    (implSeg (Impl.implC fin lRows κs₀)).linkWAll (KindP.ofSeg σ).tix tt rr =
      Array.replicate nLinkFam 0 := rfl

/-- The segment's specified `linkWAll` is `0^8`. -/
theorem linkWAll_segS (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) (tt rr : Array F) :
    (specSeg (Impl.specC fin lRows κs₀)).linkWAll (KindP.ofSeg σ).tix tt rr =
      Array.replicate nLinkFam 0 := rfl

/-- Any implementation meeting the segment's specification answers `0^8`. -/
theorem linkWAll_seg_of_meets {impl : OpImpl} {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (h : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) (tt rr : Array F) :
    impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0 := by
  rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

/-! ## The program: `linkOps` over `0^8` -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- Family `f`'s four ops (`linkOps`' body). -/
def linkFam (ks b f : ℕ) : List Op :=
  [.getF (b + 25) f, .mulF (b + (26 + 4 * f)) (b + (27 + 4 * f)),
   .addF (if f = 0 then b + 22 else b + (25 + 4 * f)) (b + (28 + 4 * f)),
   .mulF (b + (26 + 4 * f)) ks]

theorem linkOps_eq (ks b : ℕ) : linkOps ks b = (List.range' 0 8).flatMap (linkFam ks b) := by
  rw [linkOps, List.range_eq_range']; rfl

theorem rd_appL (X : Array Val) (L vs : List Val) {i : ℕ} (hi : i < X.size + L.length) :
    rd (X ++ (L ++ vs).toArray) i = rd (X ++ L.toArray) i := by
  rw [← app_app, rd_app_left _ _ (by simpa using hi)]

theorem rd_appR (X : Array Val) (L vs : List Val) (j : ℕ) :
    rd (X ++ (L ++ vs).toArray) (X.size + L.length + j) = vs.getD j default := by
  rw [← app_app, show X.size + L.length = (X ++ L.toArray).size by simp, rd_app]

/-- One pure op that yields one value and passes. -/
theorem pureRun_step {op : Op} {ops : List Op} {X : Array Val} {L : List Val} {v : Val}
    (h : evalOp impl κ inp (X ++ L.toArray) op = .vals [v] true) :
    pureRun impl κ inp (op :: ops) X L = pureRun impl κ inp ops X (L ++ [v]) := by
  simp only [pureRun, h, Bool.true_and]
  cases pureRun impl κ inp ops X (L ++ [v]) <;> rfl

/-- One family over `0^8`: it appends `0, 0, acc, pow·κ_s`. -/
theorem pureRun_linkFam (X : Array Val) (L : List Val) (ks b f : ℕ) (rest : List Op) {k p a : F}
    (hsz : X.size + L.length = b + 27 + 4 * f) (hk : ks < b + 27 + 4 * f)
    (hW : rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0))
    (hks : rd (X ++ L.toArray) ks = .f k) (hp : rd (X ++ L.toArray) (b + (26 + 4 * f)) = .f p)
    (ha : rd (X ++ L.toArray) (if f = 0 then b + 22 else b + (25 + 4 * f)) = .f a) :
    pureRun impl κ inp (linkFam ks b f ++ rest) X L =
      pureRun impl κ inp rest X (L ++ [.f 0, .f 0, .f a, .f (p * k)]) := by
  have hA : (if f = 0 then b + 22 else b + (25 + 4 * f)) < b + 27 + 4 * f := by split_ifs <;> omega
  have g0 : (Array.replicate nLinkFam (0 : F)).getD f 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split_ifs <;> rfl
  have e1 : rd (X ++ (L ++ [Val.f 0]).toArray) (b + (27 + 4 * f)) = .f 0 := by
    rw [show b + (27 + 4 * f) = X.size + L.length + 0 by omega, rd_appR]; rfl
  have e2 : rd (X ++ (L ++ [Val.f 0, Val.f 0]).toArray) (b + (28 + 4 * f)) = .f 0 := by
    rw [show b + (28 + 4 * f) = X.size + L.length + 1 by omega, rd_appR]; rfl
  simp only [linkFam, List.cons_append, List.nil_append]
  rw [pureRun_step impl κ inp (v := .f 0) (by simp only [evalOp, hW, Val.toAF, g0]),
    pureRun_step impl κ inp (v := .f 0) (by
      simp only [evalOp, rd_appL X L _ (show b + (26 + 4 * f) < X.size + L.length by omega), hp, e1,
        Val.toF, mul_zero]),
    pureRun_step impl κ inp (v := .f a) (by
      rw [List.append_assoc, List.singleton_append]
      simp only [evalOp, rd_appL X L _ (show (if f = 0 then b + 22 else b + (25 + 4 * f)) <
          X.size + L.length by omega), ha, e2, Val.toF,
        add_zero]),
    pureRun_step impl κ inp (v := .f (p * k)) (by
      rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append]
      simp only [evalOp, rd_appL X L _ (show b + (26 + 4 * f) < X.size + L.length by omega), hp,
        rd_appL X L _ (show ks < X.size + L.length by omega), hks, Val.toF])]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem pureRun_linkFams (X : Array Val) (ks b : ℕ) (rest : List Op) : ∀ (m f : ℕ) (L : List Val) (k p a : F),
    X.size + L.length = b + 27 + 4 * f → ks < b + 27 →
    rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0) →
    rd (X ++ L.toArray) ks = .f k → rd (X ++ L.toArray) (b + (26 + 4 * f)) = .f p →
    rd (X ++ L.toArray) (if f = 0 then b + 22 else b + (25 + 4 * f)) = .f a →
    ∃ M, pureRun impl κ inp ((List.range' f m).flatMap (linkFam ks b) ++ rest) X L =
        pureRun impl κ inp rest X (L ++ M) ∧ M.length = 4 * m ∧ (0 < m → M.getD (4 * m - 2) default = .f a)
  | 0, _, L, _, _, _, _, _, _, _, _, _ => ⟨[], by simp, rfl, fun h => absurd h (by omega)⟩
  | m + 1, f, L, k, p, a, hsz, hk, hW, hks, hp, ha => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc,
      pureRun_linkFam impl κ inp X L ks b f _ hsz (by omega) hW hks hp ha]
    set V : List Val := [.f 0, .f 0, .f a, .f (p * k)]
    have hl : (L ++ V).length = L.length + 4 := by simp [V]
    obtain ⟨M, h1, h2, h3⟩ := pureRun_linkFams X ks b rest m (f + 1) (L ++ V) k (p * k) a (by omega) hk
      (by rw [rd_appL X L _ (by omega)]; exact hW) (by rw [rd_appL X L _ (by omega)]; exact hks)
      (by rw [show b + (26 + 4 * (f + 1)) = X.size + L.length + 3 by omega, rd_appR]; rfl)
      (by rw [if_neg (by omega), show b + (25 + 4 * (f + 1)) = X.size + L.length + 2 by omega,
          rd_appR]; rfl)
    refine ⟨V ++ M, by rw [h1, List.append_assoc], by simp [V, h2]; ring, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · rw [List.getD_append_right _ _ _ _ (by simp [V]; omega)]
      rw [show 4 * (m + 1) - 2 - V.length = 4 * m - 2 by simp [V]; omega]
      exact h3 hm

/-- **`linkOps` over `0^8`** (a segment's `finSh`): it passes, appends 32 registers, and its
accumulator `b + 57` holds register `b + 22`'s value. -/
theorem run_linkOps_zero (X : Array Val) (L : List Val) (ks b : ℕ) {k p a : F}
    (hsz : X.size + L.length = b + 27) (hk : ks < b + 27)
    (hW : rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0))
    (hks : rd (X ++ L.toArray) ks = .f k) (hp : rd (X ++ L.toArray) (b + 26) = .f p)
    (ha : rd (X ++ L.toArray) (b + 22) = .f a) :
    ∃ M, pureRun impl κ inp (linkOps ks b) X L = some (L ++ M, true) ∧ M.length = 32 ∧
      rd (X ++ (L ++ M).toArray) (b + 57) = .f a := by
  obtain ⟨M, h1, h2, h3⟩ := pureRun_linkFams impl κ inp X ks b [] 8 0 L k p a hsz hk hW hks hp ha
  rw [List.append_nil] at h1
  refine ⟨M, by rw [linkOps_eq, h1]; rfl, h2, ?_⟩
  rw [show b + 57 = X.size + L.length + 30 by omega, rd_appR]
  exact h3 (by norm_num)

/-! ## Controls -/

/-- Control (−): a nonzero family weight does move the accumulator (`W₀ = 1`, `pow = 1`). -/
theorem linkSum_ctl : linkSum #[(1 : F)] 0 nLinkFam 0 1 = 1 := by simp [linkSum, nLinkFam]

/-- Control (+): a node's concrete `linkWAll` is the node's link weights, not `0^8`. -/
theorem linkWAll_nodeC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) (tt rr : Array F) :
    (Impl.implC fin lRows κs₀).linkWAll (KindP.ofNode ν).tix tt rr =
      NodeI.linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26) := rfl

end Run

/-! ## The proof size the program layer assumes (`runLog_chain4`'s `hπ`) -/

/-- **A node's proof has `seq4`'s size**: `kindOf4` accepts a node byte only at `piSizeOf seq4`. -/
theorem piSize_node4 {π : Proof} {ν : NodeKind} (h : kindOf4 π = .node ν) : π.size = piSizeOf seq4 := by
  unfold kindOf4 at h; dsimp only at h
  split_ifs at h <;> first | assumption | (split at h <;> simp_all)

/-- **Each segment of an aggregate has `segSize` bytes** when the aggregate passes `V_A`'s size
check (`π.size = 48 + k · segSize`). -/
theorem piSize_aggSegs {segSize k : ℕ} {π : Proof} (h : π.size = 48 + k * segSize) :
    ∀ s ∈ aggSegs segSize k π, s.size = segSize := by
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
  rw [List.mem_range] at hi
  have : 48 + (i + 1) * segSize ≤ π.size := by rw [h]; nlinarith
  simp only [ByteArray.size_extract]
  rw [Nat.min_eq_left this]; rw [Nat.add_mul]; omega


end FR.Snd.R4
