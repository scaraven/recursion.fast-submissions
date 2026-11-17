-- New for lvm2 MP-B cap pruning (CAP-VS, 2026-11-17): the S2GB driver over the schedule's atoms (`driveAtomsB`,
-- `driveItemsB_eq`), what an accepting run consumes (`drive_runB`, `drive_nextB`), the static check `stAB`, and the
-- expanded body over the atoms (`fillA`). Proof help for `refinesB_of`.
import LvmS2GBRefSimOpen

/-!
# The S2GB driver over atoms

`driveAtomsB p π as s t k`: `driveItemsB` with every item cut into its atoms, the tail cursor `t` carried along
(`driveItemsB_eq`); a cap atom `.cap c r` moves the body cursor by the sent `2^capSendBits` nodes, an opening atom is
`openLoopB`. `stAB`: `stA` with the sent caps' widths, S2GB's opening geometry (`geomOkB`) and the positions' count.
`fillA`: `fillItems` over the atoms (`fillItems_eq`); `statA`, `expA`: the static and expanded bytes of the atoms.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

section Drive

variable (p : Params) (π : ByteArray)

/-- **The S2GB driver over atoms.** -/
def driveAtomsB : List Atom → DSt → ℕ → (DSt → ℕ → OProg Bool) → OProg Bool
  | [], s, t, k => k s t
  | .rd :: as, s, t, k => driveAtomsB as { s with off := s.off + eBytes } t k
  | .rdw w :: as, s, t, k => driveAtomsB as { s with off := s.off + w } t k
  | .cap c r :: as, s, t, k =>
    driveAtomsB as { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ p.capSendBits r.lv c } t k
  | .sm :: as, s, t, k => fsQuery π s fun s _ => driveAtomsB as s t k
  | .pclr :: as, s, t, k => driveAtomsB as { s with pos := [] } t k
  | .ps h n :: as, s, t, k =>
    fsQuery π s fun s a => driveAtomsB as { s with pos := s.pos ++ chunk h n (answerBits a) } t k
  | .op r :: as, s, t, k =>
    match capOffset s r with
    | none => .ret false
    | some capOff =>
      if (p.level r).row ≤ queryCap then
        openLoopB π (p.level r) (p.capSendBits r.lv (p.level r).cap) capOff s t fun s t =>
          driveAtomsB as { s with pend := s.off } t k
      else .ret false

theorem driveAtomsB_reads (as : List Atom) (t : ℕ) (k : DSt → ℕ → OProg Bool) :
    ∀ (m : ℕ) (s : DSt), driveAtomsB p π (List.replicate m .rd ++ as) s t k =
      driveAtomsB p π as { s with off := s.off + eBytes * m } t k
  | 0, s => by simp
  | m + 1, s => by
    rw [List.replicate_succ, List.cons_append, driveAtomsB, driveAtomsB_reads as t k m]
    congr 2
    simp only [eBytes]; ring

theorem driveAtomsB_readsW (w : ℕ) (as : List Atom) (t : ℕ) (k : DSt → ℕ → OProg Bool) :
    ∀ (m : ℕ) (s : DSt), driveAtomsB p π (List.replicate m (.rdw w) ++ as) s t k =
      driveAtomsB p π as { s with off := s.off + w * m } t k
  | 0, s => by simp
  | m + 1, s => by
    rw [List.replicate_succ, List.cons_append, driveAtomsB, driveAtomsB_readsW w as t k m]
    congr 2
    ring

theorem driveAtomsB_pos (h : ℕ) (as : List Atom) (t : ℕ) (k : DSt → ℕ → OProg Bool) :
    ∀ (n rem : ℕ) (s : DSt), posLoop π h n rem s (fun s ↦ driveAtomsB p π as s t k) =
      driveAtomsB p π (posAtoms h n rem ++ as) s t k
  | 0, rem, s => rfl
  | n + 1, rem, s => by
    simp only [posLoop, posAtoms, List.cons_append, driveAtomsB, chunk]
    congr 1; funext s' a
    exact driveAtomsB_pos h as t k n _ _

/-- **`driveItemsB` is the driver over the atoms.** -/
theorem driveItemsB_eq : ∀ (its : List Item) (s : DSt) (t : ℕ) (k : DSt → ℕ → OProg Bool),
    driveItemsB p π its s t k = driveAtomsB p π (atomsOf p its) s t k
  | [], s, t, k => rfl
  | .readW m w :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms, driveAtomsB_readsW, driveItemsB, driveItemsB_eq its]
  | .read m :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms, driveAtomsB_reads, driveItemsB, driveItemsB_eq its]
  | .cap c r :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms, driveItemsB, driveItemsB_eq its]; rfl
  | .sample :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms, driveItemsB]
    simp only [List.cons_append, List.nil_append, driveAtomsB]
    congr 1; funext s' a; exact driveItemsB_eq its s' t k
  | .positions r :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms, driveItemsB, List.cons_append, driveAtomsB, ← driveAtomsB_pos]
    congr 1; funext s'; exact driveItemsB_eq its s' t k
  | .opening r :: its, s, t, k => by
    rw [atomsOf_cons, itemAtoms]
    simp only [driveItemsB, List.cons_append, List.nil_append, driveAtomsB]
    cases capOffset s r with
    | none => rfl
    | some capOff =>
      simp only
      split
      · congr 1; funext s' t'; exact driveItemsB_eq its _ t' k
      · rfl

end Drive

/-! ## What an accepting run consumes -/

/-- The bytes the atoms read before the next query, the sent caps' widths at S2GB. -/
def pendAB (p : Params) : List Atom → ℕ
  | .rd :: as => eBytes + pendAB p as
  | .rdw w :: as => w + pendAB p as
  | .cap c r :: as => nodeBytes * 2 ^ p.capSendBits r.lv c + pendAB p as
  | .pclr :: as => pendAB p as
  | _ => 0

/-- **Lookahead at S2GB**: an accepting run's next entry is the next Fiat–Shamir query. -/
theorem drive_nextB (p : Params) (π : ByteArray) :
    ∀ (as : List Atom) (s : DSt) (t : ℕ) (k : DSt → ℕ → OProg Bool) (tr : Trace), NextFS as →
      (driveAtomsB p π as s t k).runSeq tr = some true →
      ∃ a rest, tr = (digestBytes s.st ++ π.extract s.pend (s.off + pendAB p as), a) :: rest
  | .rd :: as, s, t, k, tr, hn, h => by
    obtain ⟨a, rest, e⟩ := drive_nextB p π as _ t k tr hn h
    exact ⟨a, rest, by rw [e]; simp only [pendAB, Nat.add_assoc]⟩
  | .rdw w :: as, s, t, k, tr, hn, h => by
    obtain ⟨a, rest, e⟩ := drive_nextB p π as _ t k tr hn h
    exact ⟨a, rest, by rw [e]; simp only [pendAB, Nat.add_assoc]⟩
  | .cap c r :: as, s, t, k, tr, hn, h => by
    obtain ⟨a, rest, e⟩ := drive_nextB p π as _ t k tr hn h
    exact ⟨a, rest, by rw [e]; simp only [pendAB, Nat.add_assoc]⟩
  | .pclr :: as, s, t, k, tr, hn, h => drive_nextB p π as { s with pos := [] } t k tr hn h
  | .sm :: as, s, t, k, tr, _, h => by
    obtain ⟨a, rest, e, -⟩ := runSeq_query_cons h
    exact ⟨a, rest, by simp [e, pendAB]⟩
  | .ps hh n :: as, s, t, k, tr, _, h => by
    obtain ⟨a, rest, e, -⟩ := runSeq_query_cons h
    exact ⟨a, rest, by simp [e, pendAB]⟩

/-- The paths of an opening on a trace. -/
theorem pathsB_run (π : ByteArray) (Lv : Level) : ∀ (ps : List ℕ) (s : DSt) (acc : List Digest)
    (kp : DSt → List Digest → OProg Bool) (tr : Trace), (pathsB π Lv ps s acc kp).runSeq tr = some true →
    ∃ s' tops n, (kp s' tops).runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s.off ≤ s'.off ∧ n ≤ tr.length
  | [], s, acc, kp, tr, h => ⟨s, acc.reverse, 0, h, by simp, le_rfl, by simp⟩
  | q :: qs, s, acc, kp, tr, h => by
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s1, d, n1, h1, h2, h3, h4⟩ := climb_run π q Lv.path 0 a _ _ rest h'
    obtain ⟨s', tops, n, h5, h6, h7, h8⟩ := pathsB_run π Lv qs s1 (d :: acc) kp _ h1
    refine ⟨s', tops, n1 + n + 1, ?_, ?_, ?_, ?_⟩
    · rw [drop_succ_cons, ← List.drop_drop]; exact h5
    · exact log_cons (log_comp (A := rest) (n₁ := n1) (n₂ := n) (L₀ := (_, a) :: s.log) h2 h6)
    · have : s1.off = s.off + Lv.row + nodeBytes * Lv.path := h3
      (clear * - this h7; omega)
    · have := List.length_drop (l := rest) (i := n1); simp only [List.length_cons]; (clear * - h4 h8 this; omega)

/-- The heap on a trace. -/
theorem heapB_run0 (lay : Array Digest) (m : ℕ) : ∀ (n kk : ℕ) (A : Array Digest) (s : DSt)
    (kh : DSt → Array Digest → OProg Bool) (tr : Trace), (heapB lay m n kk A s kh).runSeq tr = some true →
    ∃ s' A' n', (kh s' A').runSeq (tr.drop n') = some true ∧ s'.log = (tr.take n').reverse ++ s.log ∧
      s'.off = s.off ∧ n' ≤ tr.length
  | 0, kk, A, s, kh, tr, h => ⟨s, A, 0, h, by simp, rfl, by simp⟩
  | n + 1, kk, A, s, kh, tr, h => by
    rw [heapB] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', A', n', h1, h2, h3, h4⟩ := heapB_run0 lay m n (kk - 1) _ _ kh rest h'
    exact ⟨s', A', n' + 1, h1, log_cons h2, h3, by simp only [List.length_cons]; (clear * - h4; omega)⟩

/-- An S2GB opening on a trace. -/
theorem openLoopB_run (π : ByteArray) (Lv : Level) (c capOff : ℕ) (s : DSt) (t : ℕ)
    (kk : DSt → ℕ → OProg Bool) (tr : Trace) (h : (openLoopB π Lv c capOff s t kk).runSeq tr = some true) :
    ∃ s' t' n, (kk s' t').runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s.off ≤ s'.off ∧ n ≤ tr.length := by
  unfold openLoopB at h
  obtain ⟨s1, tops, n1, h1, h2, h3, h4⟩ := pathsB_run π Lv _ s [] _ tr h
  simp only at h1
  split at h1
  · obtain ⟨s2, A, n2, h5, h6, h7, h8⟩ := heapB_run0 _ _ _ _ _ _ _ _ h1
    try simp only at h5
    split at h5
    · refine ⟨s2, _, n1 + n2, by rw [← List.drop_drop]; exact h5, log_comp h2 h6, by (clear * - h3 h7; omega), ?_⟩
      have := List.length_drop (l := tr) (i := n1); (clear * - h4 h8 this; omega)
    · exact absurd (runSeq_ret_true h5).2 (by simp)
  · exact absurd (runSeq_ret_true h1).2 (by simp)

/-- **An accepting S2GB driver run** (`drive_run`'s twin). -/
theorem drive_runB (p : Params) (π : ByteArray) : ∀ (as : List Atom) (s : DSt) (t : ℕ)
    (k : DSt → ℕ → OProg Bool) (tr : Trace), (driveAtomsB p π as s t k).runSeq tr = some true →
    ∃ s' t' n, (k s' t').runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s.off + pendAB p as ≤ s'.off ∧ n ≤ tr.length
  | [], s, t, k, tr, h => ⟨s, t, 0, h, by simp, by simp [pendAB], by simp⟩
  | .rd :: as, s, t, k, tr, h => by
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as _ t k tr h
    exact ⟨s', t', n, h1, h2, by simp only [pendAB] at h3 ⊢; (clear * - h3; omega), h4⟩
  | .rdw w :: as, s, t, k, tr, h => by
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as _ t k tr h
    exact ⟨s', t', n, h1, h2, by simp only [pendAB] at h3 ⊢; (clear * - h3; omega), h4⟩
  | .cap c r :: as, s, t, k, tr, h => by
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as _ t k tr h
    exact ⟨s', t', n, h1, h2, by simp only [pendAB] at h3 ⊢; (clear * - h3; omega), h4⟩
  | .pclr :: as, s, t, k, tr, h => by
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as { s with pos := [] } t k tr h
    exact ⟨s', t', n, h1, h2, by simpa [pendAB] using h3, h4⟩
  | .sm :: as, s, t, k, tr, h => by
    rw [driveAtomsB, fsQuery] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as _ t k rest h'
    exact ⟨s', t', n + 1, h1, log_cons h2, by simp only [pendAB] at h3 ⊢; (clear * - h3; omega),
      by simp only [List.length_cons]; (clear * - h4; omega)⟩
  | .ps hh m :: as, s, t, k, tr, h => by
    rw [driveAtomsB, fsQuery] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', t', n, h1, h2, h3, h4⟩ := drive_runB p π as _ t k rest h'
    exact ⟨s', t', n + 1, h1, log_cons h2, by simp only [pendAB] at h3 ⊢; (clear * - h3; omega),
      by simp only [List.length_cons]; (clear * - h4; omega)⟩
  | .op r :: as, s, t, k, tr, h => by
    simp only [driveAtomsB] at h
    split at h
    · exact absurd (runSeq_ret_true h).2 (by simp)
    · split at h
      · obtain ⟨s1, t1, n1, h1, h2, h3, h4⟩ := openLoopB_run π _ _ _ _ _ _ tr h
        obtain ⟨s', t', n, h5, h6, h7, h8⟩ := drive_runB p π as _ t1 k _ h1
        refine ⟨s', t', n1 + n, by rw [← List.drop_drop]; exact h5, log_comp h2 h6, ?_, ?_⟩
        · simp only [pendAB] at h7 ⊢; (clear * - h3 h7; omega)
        · have := List.length_drop (l := tr) (i := n1); (clear * - h4 h8 this; omega)
      · exact absurd (runSeq_ret_true h).2 (by simp)

/-- The body cursor bound from an accepting S2GB run. -/
theorem bound_of_driveB {p : Params} {π : ByteArray} {tr : Trace} {as : List Atom} {s : DSt} {t : ℕ}
    {k : DSt → ℕ → OProg Bool} {i : ℕ}
    (hk : ∀ s' t' n, (k s' t').runSeq (tr.drop n) = some true → s'.off ≤ π.size)
    (h : (driveAtomsB p π as s t k).runSeq (tr.drop i) = some true) : s.off + pendAB p as ≤ π.size := by
  obtain ⟨s', t', n, h1, -, h3, -⟩ := drive_runB p π as s t k _ h
  have := hk s' t' (i + n) (by rw [← List.drop_drop]; exact h1)
  (clear * - h3 this; omega)

/-! ## The static check -/

/-- **An S2GB opening's level geometry** (`geomOk` with the cap: the cap layer is `capS`'s, the sent cap
`capOfB`'s). -/
def geomOkB (p : Params) (r : Ref) (occ : ℕ → ℕ → ℕ) : Bool :=
  let sh := shpS (idxS r)
  (p.level r).height == sh.1 && (p.level r).row == 8 * min (occ sh.1 sh.2) sh.2 &&
    (p.level r).path == sh.1 - capS sh.1 sh.2 && (p.level r).cap == capS sh.1 sh.2 &&
    p.capSendBits r.lv (p.level r).cap == Lvm.ASM.capOfB sh.1 sh.2 &&
    decide (Lvm.ASM.capOfB sh.1 sh.2 ≤ capS sh.1 sh.2)

/-- **The static facts of the atoms at S2GB** (`stA` with the sent caps' widths and their levels `capOfB`,
`geomOkB`, and `np` positions since the last positions marker, `t` at an opening). -/
def stAB (p : Params) (occ : ℕ → ℕ → ℕ) : List Atom → ℕ → List Ref → List ℕ → ℕ → Bool
  | [], pend, _, _, _ => pend == 0
  | .rd :: as, pend, cr, hs, np => stAB p occ as (pend + eBytes) cr hs np
  | .rdw w :: as, pend, cr, hs, np => stAB p occ as (pend + w) cr hs np
  | .cap c r :: as, pend, cr, hs, np =>
    (idxS r == cr.length) && !(cr.contains r) &&
      (p.capSendBits r.lv c == Lvm.ASM.capOfB (shpS (idxS r)).1 (shpS (idxS r)).2) &&
      stAB p occ as (pend + nodeBytes * 2 ^ p.capSendBits r.lv c) (cr ++ [r]) hs np
  | .sm :: as, pend, cr, hs, np => decide (32 + pend ≤ queryCap) && stAB p occ as 0 cr hs np
  | .pclr :: as, pend, cr, _, _ => stAB p occ as pend cr [] 0
  | .ps h n :: as, pend, cr, hs, np => decide (32 + pend ≤ queryCap) && stAB p occ as 0 cr (h :: hs) (np + n)
  | .op r :: as, pend, cr, hs, np =>
    (pend == 0) && cr.contains r && geomOkB p r occ && hs.all (· == (shpS (idxS r)).1) &&
      (np == (p.level r).t) && stAB p occ as 0 cr hs np

/-- After pending bytes, a Fiat–Shamir query comes (S2GB). -/
theorem nextFS_of_stAB {p : Params} {occ : ℕ → ℕ → ℕ} : ∀ (as : List Atom) (pend : ℕ) (cr : List Ref)
    (hs : List ℕ) (np : ℕ), stAB p occ as pend cr hs np = true → 0 < pend → NextFS as
  | [], pend, _, _, _, h, hp => by simp only [stAB, beq_iff_eq] at h; omega
  | .rd :: as, pend, cr, hs, np, h, _ => nextFS_of_stAB as _ cr hs np h (by simp [eBytes])
  | .rdw _ :: as, _, cr, hs, np, h, hp => nextFS_of_stAB as _ cr hs np h (by omega)
  | .cap c r :: as, pend, cr, hs, np, h, _ => by
    simp only [stAB, Bool.and_eq_true] at h
    exact nextFS_of_stAB as _ _ hs np h.2 (by simp only [nodeBytes]; positivity)
  | .sm :: _, _, _, _, _, _, _ => trivial
  | .pclr :: as, pend, cr, hs, np, h, hp => nextFS_of_stAB as pend cr [] 0 h hp
  | .ps _ _ :: _, _, _, _, _, _, _ => trivial
  | .op r :: as, pend, cr, hs, np, h, hp => by
    simp only [stAB, Bool.and_eq_true, beq_iff_eq] at h; (clear * - hp h; omega)

/-- `stAB` over the `ps` atoms of a positions item, then `k`. -/
def stPosB (h : ℕ) : ℕ → ℕ → ℕ → List ℕ → ℕ → (ℕ → List ℕ → ℕ → Bool) → Bool
  | 0, _, pend, hs, np, k => k pend hs np
  | n + 1, rem, pend, hs, np, k => decide (32 + pend ≤ queryCap) &&
      stPosB h n (rem - min positionsPerAnswer rem) 0 (h :: hs) (np + min positionsPerAnswer rem) k

/-- **`stAB` on the items** (`stAB_atomsOf`). -/
def stIB (p : Params) (occ : ℕ → ℕ → ℕ) : List Item → ℕ → List Ref → List ℕ → ℕ → Bool
  | [], pend, _, _, _ => pend == 0
  | .read m :: its, pend, cr, hs, np => stIB p occ its (pend + eBytes * m) cr hs np
  | .readW m w :: its, pend, cr, hs, np => stIB p occ its (pend + w * m) cr hs np
  | .cap c r :: its, pend, cr, hs, np =>
    (idxS r == cr.length) && !(cr.contains r) &&
      (p.capSendBits r.lv c == Lvm.ASM.capOfB (shpS (idxS r)).1 (shpS (idxS r)).2) &&
      stIB p occ its (pend + nodeBytes * 2 ^ p.capSendBits r.lv c) (cr ++ [r]) hs np
  | .sample :: its, pend, cr, hs, np => decide (32 + pend ≤ queryCap) && stIB p occ its 0 cr hs np
  | .positions r :: its, pend, cr, _, _ =>
    stPosB (p.level r).height (p.level r).nPosQ (p.level r).t pend [] 0 fun pend hs np => stIB p occ its pend cr hs np
  | .opening r :: its, pend, cr, hs, np =>
    (pend == 0) && cr.contains r && geomOkB p r occ && hs.all (· == (shpS (idxS r)).1) &&
      (np == (p.level r).t) && stIB p occ its 0 cr hs np

theorem stAB_reads (p : Params) (occ : ℕ → ℕ → ℕ) (as : List Atom) (cr : List Ref) (hs : List ℕ) (np : ℕ) :
    ∀ (m pend : ℕ), stAB p occ (List.replicate m .rd ++ as) pend cr hs np = stAB p occ as (pend + eBytes * m) cr hs np
  | 0, pend => rfl
  | m + 1, pend => by
    rw [List.replicate_succ, List.cons_append, stAB, stAB_reads p occ as cr hs np m, Nat.mul_succ]
    congr 1
    omega

theorem stAB_readsW (p : Params) (occ : ℕ → ℕ → ℕ) (w : ℕ) (as : List Atom) (cr : List Ref) (hs : List ℕ)
    (np : ℕ) : ∀ (m pend : ℕ), stAB p occ (List.replicate m (.rdw w) ++ as) pend cr hs np =
      stAB p occ as (pend + w * m) cr hs np
  | 0, pend => rfl
  | m + 1, pend => by
    rw [List.replicate_succ, List.cons_append, stAB, stAB_readsW p occ w as cr hs np m, Nat.mul_succ]
    congr 1
    omega

theorem stAB_pos (p : Params) (occ : ℕ → ℕ → ℕ) (as : List Atom) (cr : List Ref) (h : ℕ) :
    ∀ (n rem pend : ℕ) (hs : List ℕ) (np : ℕ), stAB p occ (posAtoms h n rem ++ as) pend cr hs np =
      stPosB h n rem pend hs np fun pend hs np => stAB p occ as pend cr hs np
  | 0, _, _, _, _ => rfl
  | n + 1, rem, pend, hs, np => by
    rw [posAtoms, List.cons_append, stAB, stAB_pos p occ as cr h n, stPosB]

/-- `stAB` over a schedule's atoms is `stIB` over its items. -/
theorem stAB_atomsOf (p : Params) (occ : ℕ → ℕ → ℕ) : ∀ (its : List Item) (pend : ℕ) (cr : List Ref)
    (hs : List ℕ) (np : ℕ), stAB p occ (atomsOf p its) pend cr hs np = stIB p occ its pend cr hs np
  | [], _, _, _, _ => rfl
  | it :: its, pend, cr, hs, np => by
    rw [atomsOf_cons]
    cases it with
    | read m => rw [itemAtoms, stAB_reads, stIB, stAB_atomsOf p occ its]
    | readW m w => rw [itemAtoms, stAB_readsW, stIB, stAB_atomsOf p occ its]
    | cap c r => rw [itemAtoms, List.singleton_append, stAB, stIB, stAB_atomsOf p occ its]
    | sample => rw [itemAtoms, List.singleton_append, stAB, stIB, stAB_atomsOf p occ its]
    | positions r =>
      rw [itemAtoms, List.cons_append, stAB, stAB_pos, stIB]
      congr 1
      funext pend hs np
      exact stAB_atomsOf p occ its pend cr hs np
    | opening r => rw [itemAtoms, List.singleton_append, stAB, stIB, stAB_atomsOf p occ its]

/-! ## The expanded body over the atoms -/

/-- **The expanded body over the atoms** (`fillItems`'s atom form). -/
def fillA (p : Params) (b : List UInt8) : List Atom → ℕ → List UInt8 → List UInt8
  | [], _, _ => []
  | .rd :: as, o, w => (b.drop o).take eBytes ++ fillA p b as (o + eBytes) w
  | .rdw x :: as, o, w => (b.drop o).take x ++ fillA p b as (o + x) w
  | .cap c r :: as, o, w =>
    (b.drop o).take (nodeBytes * 2 ^ p.capSendBits r.lv c) ++
      fillA p b as (o + nodeBytes * 2 ^ p.capSendBits r.lv c) w
  | .sm :: as, o, w => fillA p b as o w
  | .pclr :: as, o, w => fillA p b as o w
  | .ps _ _ :: as, o, w => fillA p b as o w
  | .op r :: as, o, w =>
    fillPaths b ((p.level r).row + nodeBytes * (p.level r).path)
        (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap)) (p.level r).t o w ++
      fillA p b as (o + (p.level r).t * ((p.level r).row + nodeBytes * (p.level r).path))
        (w.drop ((p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap))))

/-- The static bytes of the atoms. -/
def statA (p : Params) : List Atom → ℕ
  | [] => 0
  | .rd :: as => eBytes + statA p as
  | .rdw x :: as => x + statA p as
  | .cap c r :: as => nodeBytes * 2 ^ p.capSendBits r.lv c + statA p as
  | .sm :: as => statA p as
  | .pclr :: as => statA p as
  | .ps _ _ :: as => statA p as
  | .op r :: as => (p.level r).t * ((p.level r).row + nodeBytes * (p.level r).path) + statA p as

/-- The upper-sibling bytes of the atoms. -/
def expA (p : Params) : List Atom → ℕ
  | [] => 0
  | .rd :: as => expA p as
  | .rdw _ :: as => expA p as
  | .cap _ _ :: as => expA p as
  | .sm :: as => expA p as
  | .pclr :: as => expA p as
  | .ps _ _ :: as => expA p as
  | .op r :: as =>
    (p.level r).t * (nodeBytes * ((p.level r).cap - p.capSendBits r.lv (p.level r).cap)) + expA p as

theorem fillA_reads (p : Params) (b : List UInt8) (as : List Atom) (w : List UInt8) :
    ∀ (m o : ℕ), fillA p b (List.replicate m .rd ++ as) o w = (b.drop o).take (eBytes * m) ++
      fillA p b as (o + eBytes * m) w
  | 0, o => by simp
  | m + 1, o => by
    rw [List.replicate_succ, List.cons_append, fillA, fillA_reads p b as w m, show eBytes * (m + 1) = eBytes + eBytes * m
      by ring, List.take_add, List.drop_drop, List.append_assoc, Nat.add_assoc]

theorem fillA_readsW (p : Params) (b : List UInt8) (x : ℕ) (as : List Atom) (w : List UInt8) :
    ∀ (m o : ℕ), fillA p b (List.replicate m (.rdw x) ++ as) o w = (b.drop o).take (x * m) ++
      fillA p b as (o + x * m) w
  | 0, o => by simp
  | m + 1, o => by
    rw [List.replicate_succ, List.cons_append, fillA, fillA_readsW p b x as w m, show x * (m + 1) = x + x * m
      by ring, List.take_add, List.drop_drop, List.append_assoc, Nat.add_assoc]

theorem fillA_pos (p : Params) (b : List UInt8) (h : ℕ) (as : List Atom) (w : List UInt8) :
    ∀ (n rem o : ℕ), fillA p b (posAtoms h n rem ++ as) o w = fillA p b as o w
  | 0, _, _ => rfl
  | n + 1, rem, o => by rw [posAtoms, List.cons_append, fillA, fillA_pos p b h as w n]

/-- **`fillItems` is `fillA` over the atoms.** -/
theorem fillItems_eq (p : Params) (b : List UInt8) : ∀ (its : List Item) (o : ℕ) (w : List UInt8),
    fillItems p b its o w = fillA p b (atomsOf p its) o w
  | [], _, _ => rfl
  | it :: its, o, w => by
    rw [atomsOf_cons]
    cases it with
    | read m => rw [itemAtoms, fillA_reads, fillItems, fillItems_eq p b its]
    | readW m x => rw [itemAtoms, fillA_readsW, fillItems, fillItems_eq p b its]
    | cap c r => rw [itemAtoms, List.singleton_append, fillA, fillItems, fillItems_eq p b its]
    | sample => rw [itemAtoms, List.singleton_append, fillA, fillItems, fillItems_eq p b its]
    | positions r => rw [itemAtoms, List.cons_append, fillA, fillA_pos, fillItems, fillItems_eq p b its]
    | opening r => rw [itemAtoms, List.singleton_append, fillA, fillItems, fillItems_eq p b its]

theorem length_fillPaths (b : List UInt8) (n u : ℕ) : ∀ (k o : ℕ) (w : List UInt8), o + k * n ≤ b.length →
    k * u ≤ w.length → (fillPaths b n u k o w).length = k * (n + u)
  | 0, _, _, _, _ => by simp [fillPaths]
  | k + 1, o, w, h1, h2 => by
    rw [Nat.succ_mul] at h1 h2
    rw [fillPaths, List.length_append, List.length_append, length_fillPaths b n u k (o + n) (w.drop u)
      (by (clear * - h1; omega)) (by rw [List.length_drop]; (clear * - h2; omega))]
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by (clear * - h1; omega)), Nat.min_eq_left (by (clear * - h2; omega))]
    ring

theorem fillPaths_append (b : List UInt8) (n u : ℕ) : ∀ (k o : ℕ) (w w' : List UInt8), w.length = k * u →
    fillPaths b n u k o (w ++ w') = fillPaths b n u k o w
  | 0, _, _, _, _ => rfl
  | k + 1, o, w, w', h => by
    rw [fillPaths, fillPaths, List.take_append_of_le_length (by rw [h]; (clear * -; nlinarith)),
      List.drop_append_of_le_length (by rw [h]; (clear * -; nlinarith)),
      fillPaths_append b n u k (o + n) (w.drop u) w' (by rw [List.length_drop, h]; (clear * -; rw [Nat.succ_mul]; omega))]

/-- **The expanded body's length**. -/
theorem length_fillA (p : Params) (b : List UInt8) : ∀ (as : List Atom) (o : ℕ) (w : List UInt8),
    o + statA p as ≤ b.length → w.length = expA p as → (fillA p b as o w).length = statA p as + expA p as
  | [], _, _, _, _ => by simp [fillA, statA, expA]
  | .rd :: as, o, w, h1, h2 => by
    simp only [fillA, statA, expA] at h1 h2 ⊢
    rw [List.length_append, length_fillA p b as _ w (by (clear * - h1; omega)) h2]
    simp only [List.length_take, List.length_drop]; (clear * - h1; omega)
  | .rdw x :: as, o, w, h1, h2 => by
    simp only [fillA, statA, expA] at h1 h2 ⊢
    rw [List.length_append, length_fillA p b as _ w (by (clear * - h1; omega)) h2]
    simp only [List.length_take, List.length_drop]; (clear * - h1; omega)
  | .cap c r :: as, o, w, h1, h2 => by
    simp only [fillA, statA, expA] at h1 h2 ⊢
    rw [List.length_append, length_fillA p b as _ w (by (clear * - h1; omega)) h2]
    simp only [List.length_take, List.length_drop]; (clear * - h1; omega)
  | .sm :: as, o, w, h1, h2 => length_fillA p b as o w h1 h2
  | .pclr :: as, o, w, h1, h2 => length_fillA p b as o w h1 h2
  | .ps _ _ :: as, o, w, h1, h2 => length_fillA p b as o w h1 h2
  | .op r :: as, o, w, h1, h2 => by
    simp only [fillA, statA, expA] at h1 h2 ⊢
    rw [List.length_append, length_fillA p b as _ _ (by (clear * - h1; omega))
      (by rw [List.length_drop, h2]; (clear * -; omega)),
      length_fillPaths b _ _ _ _ _ (by (clear * - h1; omega)) (by rw [h2]; (clear * -; omega))]
    ring

theorem expA_append (p : Params) : ∀ (as bs : List Atom), expA p (as ++ bs) = expA p as + expA p bs
  | [], bs => by simp [expA]
  | x :: as, bs => by
    cases x <;> simp only [List.cons_append, expA, expA_append p as bs] <;> (clear * -; omega)

theorem expA_rep_rd (p : Params) : ∀ m : ℕ, expA p (List.replicate m .rd) = 0
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, expA, expA_rep_rd p m]

theorem expA_rep_rdw (p : Params) (x : ℕ) : ∀ m : ℕ, expA p (List.replicate m (.rdw x)) = 0
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, expA, expA_rep_rdw p x m]

theorem expA_posAtoms (p : Params) (h : ℕ) : ∀ n rem : ℕ, expA p (posAtoms h n rem) = 0
  | 0, _ => rfl
  | n + 1, rem => by rw [posAtoms, expA, expA_posAtoms p h n]

theorem foldl_expA (p : Params) (f : ℕ → Item → ℕ) (hf : ∀ a it, f a it = a + expA p (itemAtoms p it)) :
    ∀ (its : List Item) (a : ℕ), its.foldl f a = a + expA p (atomsOf p its)
  | [], a => by simp [expA]
  | it :: its, a => by
    rw [List.foldl_cons, foldl_expA p f hf its, hf, atomsOf_cons, expA_append]; (clear * -; omega)

/-- **The expanded bytes of a schedule are `expA` of its atoms.** -/
theorem expandBytes_eq (p : Params) : expandBytes p = expA p (atomsOf p (schedule p)) := by
  unfold expandBytes
  rw [foldl_expA p _ ?_ (schedule p) 0, Nat.zero_add]
  intro a it
  cases it <;> simp [itemAtoms, expA, expA_rep_rd, expA_rep_rdw, expA_posAtoms]

end Lvm.VEq
