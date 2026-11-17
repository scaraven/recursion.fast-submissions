-- New for lvm2 MP-B cap pruning (CAP-V, 2026-11-17): V_S's S2GB driver (`driveB`: paths to `D`, layer, heap, sent
-- caps, tail) and the compiled verifier of `schemeSWB fmtB20` on the expanded proof `fillB P20B π w`. Proof-help
-- statement for `refinesB20` (V's own; not frozen).
import LvmS2GBFill
import LvmS2GBRefSimSt

/-!
# The S2GB driver and the compiled verifier on the expanded proof (owner V)

* **`refinesB_of`**: `refines_seqOfGP`'s S2GB twin, on logs. If V_S's S2GB driver accepts `π` on `L` with a decision
  `D` whose program `prog` refines `P_S` on the S2GB stream (`RefAtPWB` at `capOfB`, `pthB`, `hqB`, `rwB20`) and
  `P_S` follows the S2GB schedule (`Fol` at `capS`), the compiled verifier of `schemeSWB fmtB20` accepts the
  expanded proof `fillB P20B π w` on `L`, `w` the paths' upper siblings (heap answers and layer nodes).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.ASM (capOfB schemeSWB)
open Lvm.CT (occOfU fmtB20)

/-! ## An opening of the S2GB driver against the compiled opening -/

/-- **After the paths of an S2GB opening** (any layer `lt`): the covered check, the heap on the trace and the cap
check held; the heap's answers are the log's. -/
theorem tailB_run (π : ByteArray) (L : Log) (tr : Trace) (hc : LogCons L tr) (Lv : Level) (c capOff : ℕ)
    (hcc : 2 ^ c ≤ 2 ^ Lv.cap) (hc1 : 1 ≤ 2 ^ c) (ps : List ℕ) (tops : List Digest) (lt : Array Digest × ℕ)
    (s1 : DSt) (j : ℕ) (kk : DSt → ℕ → OProg Bool)
    (h : (if (ps.zip tops).all (fun e => e.2 == lt.1.getD (e.1 >>> Lv.path) zeroDigest) then
        heapB lt.1 Lv.cap (2 ^ Lv.cap - 2 ^ c) (2 ^ Lv.cap - 1) (Array.replicate (2 ^ Lv.cap) zeroDigest) s1
          fun s A => if (List.range (2 ^ c)).all
            (fun i => nodeB lt.1 A Lv.cap (2 ^ c + i) == digestAt π (capOff + nodeBytes * i)) then kk s lt.2
            else .ret false
      else .ret false).runSeq (tr.drop j) = some true) :
    ∃ s2 A, (kk s2 lt.2).runSeq (tr.drop (j + (2 ^ Lv.cap - 2 ^ c))) = some true ∧ s2.off = s1.off ∧
      s2.st = s1.st ∧ s2.pend = s1.pend ∧ s2.caps = s1.caps ∧ s2.pos = s1.pos ∧
      entOff tr (j + (2 ^ Lv.cap - 2 ^ c)) = entOff tr j + 104 * (2 ^ Lv.cap - 2 ^ c) ∧
      (ps.zip tops).all (fun e => e.2 == lt.1.getD (e.1 >>> Lv.path) zeroDigest) = true ∧
      HeapOK L lt.1 A Lv.cap c ∧
      (List.range (2 ^ c)).all (fun i => nodeB lt.1 A Lv.cap (2 ^ c + i) == digestAt π (capOff + nodeBytes * i)) =
        true := by
  split_ifs at h with hcov
  · obtain ⟨s2, A, h2, ho2, hst2, hpe2, hca2, hpo2, he2, -, -, hH2⟩ :=
      heapB_run L tr hc lt.1 Lv.cap (2 ^ Lv.cap - 2 ^ c) (2 ^ Lv.cap - 1) _ s1 j _
        (by (clear * - hc1; omega)) (by simp only [Array.size_replicate]; (clear * - hcc hc1; omega)) h
    split_ifs at h2 with hcapc
    · refine ⟨s2, A, h2, ho2, hst2, hpe2, hca2, hpo2, he2, hcov, fun k hk1 hk2 ↦ ?_, hcapc⟩
      rw [nodeB_lt hk2]
      have hk := hH2 k
      generalize 2 ^ Lv.cap = P at hk hk2 hcc
      generalize 2 ^ c = Q at hk hk1 hcc hc1
      exact hk (by (clear * - hk1 hk2 hcc hc1; omega)) (by (clear * - hk2; omega))
    · exact absurd (runSeq_ret_true h2).2 (by simp)
  · exact absurd (runSeq_ret_true h).2 (by simp)

/-- **The compiled opening after an S2GB opening's checks** (any layer `lay`, heap `A`): the paths' tops are the
covered layer nodes, the heap answers on the log, the cap nodes are the sent ones. -/
theorem openSpecB (S : Scheme) (π : ByteArray) (L : Log) (Lv : Level) (c capOff ht wd : ℕ)
    (hrow : Lv.row = 8 * min (S.occ ht wd) wd) (hpath : Lv.path + Lv.cap = ht) (hcm : c ≤ Lv.cap)
    (hlv : S.capOf ht wd = c) (ps : List ℕ) (o : ℕ) (lay : Array Digest) (tops : List Digest) (A : Array Digest)
    (rows : List (List K)) (hlt : ∀ q ∈ ps, q < 2 ^ ht) (hl1 : tops.length = ps.length)
    (hcov : (ps.zip tops).all (fun e => e.2 == lay.getD (e.1 >>> Lv.path) zeroDigest) = true)
    (hH : HeapOK L lay A Lv.cap c)
    (hcapc : (List.range (2 ^ c)).all (fun i => nodeB lay A Lv.cap (2 ^ c + i) == digestAt π (capOff + nodeBytes * i))
      = true)
    (hP1 : PathsOK L π S.decK Lv.row Lv.path wd (S.occ ht wd) ps o tops rows) (R : List UInt8) :
    (S.openAll (S.capI ht wd ((blb π).drop capOff)) ps
      (fillPaths (blb π) (Lv.row + 32 * Lv.path) (32 * (Lv.cap - c)) ps.length o (wOf lay A Lv.cap c Lv.path ps) ++
        R)).runLog L = some (some (rows, R)) := by
  have htops : tops = ps.map fun q ↦ nodeB lay A Lv.cap (2 ^ Lv.cap + (q >>> Lv.path)) := by
    have hall := List.all_eq_true.mp hcov
    apply List.ext_getElem (by rw [hl1, List.length_map])
    intro j hj1 hj2
    have hj0 : j < ps.length := by rw [← hl1]; exact hj1
    have := hall (ps[j], tops[j]) (List.mem_iff_getElem.mpr ⟨j, by simp [hl1]; exact hj0, by simp⟩)
    simp only [beq_iff_eq] at this
    rw [List.getElem_map, nodeB_lay, this]
  have hcap : ∀ j < 2 ^ c, (S.capI ht wd ((blb π).drop capOff)).cap[j]? =
      some (nodeB lay A Lv.cap (2 ^ c + j)) := by
    intro j hj
    have := List.all_eq_true.mp hcapc j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at this
    rw [cap_get S π ht wd capOff j (by rw [hlv]; exact hj), this]
  rw [htops] at hP1
  exact openAll_specB S L π (S.capI ht wd ((blb π).drop capOff)) lay A Lv.cap c Lv.path hH hcm
    (by simp only [capI_ht]; (clear * - hpath; omega)) (by simp only [capI_lv]; exact hlv) hcap Lv.row
    (by simp only [Scheme.lb, capI_ht, capI_wd]; exact hrow.symm) ps o _ R
    (by simp only [capI_ht]; exact hlt) hP1

/-- **An S2GB opening in lockstep with the compiled opening**: the driver's `openLoopB` on the trace (paths,
layer, covered check, heap, cap check), the compiled `openAll` on the log over the expanded paths (`fillPaths`, the
upper siblings `w`): the same rows, the stream cursor past the paths' and the heap's entries. -/
theorem openLoopB_sim (S : Scheme) (π : ByteArray) (L : Log) (tr : Trace) (hc : LogCons L tr)
    (hdecK : S.decK = kOfBytes) (Lv : Level) (c capOff ht wd : ℕ) (hrow : Lv.row = 8 * min (S.occ ht wd) wd)
    (hpath : Lv.path + Lv.cap = ht) (hcm : c ≤ Lv.cap) (hlv : S.capOf ht wd = c) :
    ∀ (s : DSt) (t i : ℕ) (kk : DSt → ℕ → OProg Bool), (∀ q ∈ s.pos, q < 2 ^ ht) →
    (∀ s' t' n, (kk s' t').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (openLoopB π Lv c capOff s t kk).runSeq (tr.drop i) = some true →
    ∃ s' t' n, (kk s' t').runSeq (tr.drop (i + n)) = some true ∧
      s'.off = s.off + s.pos.length * (Lv.row + 32 * Lv.path) ∧ s'.st = s.st ∧ s'.pend = s.pend ∧
      s'.caps = s.caps ∧ s'.pos = s.pos ∧
      (opRows (traceBytesB tr) wd (S.occ ht wd) Lv.path s.pos.length (entOff tr i)).2 + 104 * (2 ^ Lv.cap - 2 ^ c) =
        entOff tr (i + n) ∧
      ∃ w : List UInt8, w.length = s.pos.length * (32 * (Lv.cap - c)) ∧ ∀ R : List UInt8,
        (S.openAll (S.capI ht wd ((blb π).drop capOff)) s.pos
          (fillPaths (blb π) (Lv.row + 32 * Lv.path) (32 * (Lv.cap - c)) s.pos.length s.off w ++ R)).runLog L =
          some (some ((opRows (traceBytesB tr) wd (S.occ ht wd) Lv.path s.pos.length (entOff tr i)).1, R)) := by
  intro s t i kk hlt hk h
  have hcc : 2 ^ c ≤ 2 ^ Lv.cap := Nat.pow_le_pow_right (by norm_num) hcm
  have hc1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  unfold openLoopB at h
  obtain ⟨s1, tops, n1, h1, ho1, hst1, hpe1, hca1, hpo1, hl1, he1, hP1⟩ :=
    pathsB_simL π L tr hc S.decK hdecK Lv wd (S.occ ht wd) hrow s.pos s [] i _ (fun s' tops n hh ↦ by
      simp only at hh
      split_ifs at hh
      · obtain ⟨s2, A, n2, h5, -, h7, -⟩ := heapB_run0 _ _ _ _ _ _ _ _ hh
        try simp only at h5
        split_ifs at h5
        · have := hk _ _ (n + n2) (by rw [← List.drop_drop]; exact h5)
          rw [h7] at this; exact this
        · exact absurd (runSeq_ret_true h5).2 (by simp)
      · exact absurd (runSeq_ret_true hh).2 (by simp)) h
  simp only [List.reverse_nil, List.nil_append] at h1
  obtain ⟨s2, A, h2, ho2, hst2, hpe2, hca2, hpo2, he2, hcov, hH, hcapc⟩ :=
    tailB_run π L tr hc Lv c capOff hcc hc1 _ _ _ s1 (i + n1) kk h1
  exact ⟨s2, _, n1 + (2 ^ Lv.cap - 2 ^ c), by rw [← Nat.add_assoc]; exact h2, by rw [ho2, ho1],
    by rw [hst2, hst1], by rw [hpe2, hpe1], by rw [hca2, hca1], by rw [hpo2, hpo1],
    by rw [he1, ← Nat.add_assoc, he2], _, length_wOf _ _ _ _ _ _,
    openSpecB S π L Lv c capOff ht wd hrow hpath hcm hlv s.pos s.off _ tops A _ hlt hl1 hcov hH hcapc hP1⟩

/-! ## The simulation at S2GB -/

theorem capI_fill (S : Scheme) (ht w : ℕ) (l r : List UInt8)
    (h : (l.take (S.capBytes ht w)).length = S.capBytes ht w) :
    S.capI ht w (l.take (S.capBytes ht w) ++ r) = S.capI ht w l := by
  simp only [Scheme.capI, List.take_left' h]

section Main

variable {S : Scheme} {π : ByteArray} {tr : Trace} {p : Params}

/-- **The simulation at S2GB** (`simW`'s twin): V_S's S2GB driver over the atoms on the trace, the compiled run on
the log over the expanded body `fillA … w` (the upper siblings `w` of the openings it meets), the program read off
the stream (`ivpWB`). -/
theorem simWB (hdecE : S.decE = eOfBytes) (hchal : S.chal = chalOf) (hdecK : S.decK = kOfBytes)
    (hcap : S.capOf = Lvm.ASM.capOfB) {occ : ℕ → ℕ → ℕ} (hocc : S.occ = occ) (L : Log) (hc : LogCons L tr) :
    ∀ (as : List Atom) {α : Type} (P : VerifierProgram α) (pp : List ℕ)
    (Q : α → List ℕ → Prop) (s : DSt) (t : ℕ) (st : Digest) (buf : List UInt8) (caps : List CapI)
    (rs : RS) (i : ℕ) (cr : List Ref) (hs : List ℕ) (np : ℕ) (k : DSt → ℕ → OProg Bool)
    (a : α) (rs' : RS) (ri ri' : ℕ),
    Fol capS shpS idxS P as pp Q → stAB p occ as (s.off - s.pend) cr hs np = true →
    J S π tr s st buf caps ((blb π).drop s.off) rs i cr → s.pos = pp → pp.length = np → PosOK pp hs →
    (∀ s' t' n, (k s' t').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (driveAtomsB p π as s t k).runSeq (tr.drop i) = some true → WAt S.rw ri (widthsA as) →
    ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw P (traceBytesB tr) rs ri = (some a, rs', ri') →
    ∃ (wv : List UInt8) (s' : DSt) (t' : ℕ) (st' : Digest) (buf' : List UInt8) (caps' : List CapI) (i' : ℕ)
      (cr' : List Ref), J S π tr s' st' buf' caps' ((blb π).drop s'.off) rs' i' cr' ∧
      (k s' t').runSeq (tr.drop i') = some true ∧ Q a s'.pos ∧ s'.off = s.off + statA p as ∧
      wv.length = expA p as ∧
      ∀ kS : α → Digest → List UInt8 → List CapI → List UInt8 → OProg Bool,
        (runKW S ri P st buf caps (fillA p (blb π) as s.off wv) kS).runLog L = (kS a st' buf' caps' []).runLog L
  | [], α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, _, _, _, hd, _,
      hiv => by
    cases P with
    | ret b =>
      simp only [ivpWB, Prod.mk.injEq, Option.some.injEq] at hiv
      obtain ⟨rfl, rfl, -⟩ := hiv
      exact ⟨[], s, t, st, buf, caps, i, cr, hJ, hd, hpos ▸ hF, by simp [statA], rfl, fun kS ↦ rfl⟩
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .rd :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl, hpk,
      hk, hd, hw, hiv => by
    cases P with
    | read k' =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      have hpo := hJ.pend
      have hst' : stAB p occ as (s.off - s.pend + eBytes) cr hs np = true := hst
      have hd' : (driveAtomsB p π as { s with off := s.off + eBytes } t k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_driveB hk hd'
      simp only at hb
      have hnext : NextFS (Atom.rd :: as) := nextFS_of_stAB as _ cr hs np hst' (by simp [eBytes])
      obtain ⟨a₀, rest, hdrop⟩ := drive_nextB p π (Atom.rd :: as) s t k _ hnext hd
      have hval : sbs (traceBytesB tr) (rs.ent + 40 + rs.msg) 24 = ((blb π).drop s.off).take 24 := by
        rw [hJ.ent, hJ.msg]
        exact msg_bytes hdrop (by simp only [pendAB, eBytes] at hb ⊢; (clear * - hb; omega)) hpo
          (by simp only [pendAB, eBytes]; (clear * -; omega))
      have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw (k' (eOfBytes (((blb π).drop s.off).take 24)))
          (traceBytesB tr) { rs with msg := rs.msg + 24 } (ri + 1) = (some a, rs', ri') := by
        simp only [ivpWB, hw0, hval] at hiv; exact hiv
      have h24 : s.off + 24 ≤ π.size := by simp only [eBytes] at hb; (clear * - hb; omega)
      have hT : (((blb π).drop s.off).take 24).length = 24 := take_drop_blb h24
      have hJ' : J S π tr { s with off := s.off + eBytes } st (buf ++ ((blb π).drop s.off).take 24) caps
          ((blb π).drop (s.off + eBytes)) { rs with msg := rs.msg + 24 } i cr := by
        refine ⟨hJ.st, by simp only; (clear * - hpo; omega), by simp only [eBytes]; (clear * - h24; omega), ?_, rfl,
          hJ.ent, ?_, hJ.caps⟩
        · simp only [eBytes]; rw [hJ.buf, buf_ext _ hpo]
        · simp only [eBytes]; rw [hJ.msg]; (clear * - hpo; omega)
      obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
        simWB hdecE hchal hdecK hcap hocc L hc as (k' _) pp Q _ t st _ caps _ i cr hs np k a rs' (ri + 1) ri' (hF' _)
          (by simp only; rw [show s.off + eBytes - s.pend = s.off - s.pend + eBytes by (clear * - hpo; omega)]
              exact hst')
          hJ' hpos hpl hpk hk hd' hw' hiv'
      refine ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; simp only [statA]; (clear * -; omega),
        h5, fun kS ↦ ?_⟩
      have hlen : ¬ (fillA p (blb π) (.rd :: as) s.off wv).length < 24 := by
        rw [fillA, List.length_append]; simp only [eBytes]; rw [hT]; (clear * -; omega)
      simp only [runKW, hw0, hlen, ↓reduceIte, hdecE]
      rw [show fillA p (blb π) (.rd :: as) s.off wv = ((blb π).drop s.off).take 24 ++ fillA p (blb π) as (s.off + eBytes) wv
        from rfl, List.take_left' hT, List.drop_left' hT]
      exact h6 kS
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .rdw w :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl,
      hpk, hk, hd, hw, hiv => by
    cases P with
    | read k' =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      have hpo := hJ.pend
      have hst' : stAB p occ as (s.off - s.pend + w) cr hs np = true := hst
      have hd' : (driveAtomsB p π as { s with off := s.off + w } t k).runSeq (tr.drop i) = some true := hd
      have hb := bound_of_driveB hk hd'
      simp only at hb
      have hwp := S.rw_pos ri
      have hnext : NextFS (Atom.rdw w :: as) :=
        nextFS_of_stAB as _ cr hs np hst' (by (clear * - hw0 hwp; omega))
      obtain ⟨a₀, rest, hdrop⟩ := drive_nextB p π (Atom.rdw w :: as) s t k _ hnext hd
      have hval : sbs (traceBytesB tr) (rs.ent + 40 + rs.msg) w = ((blb π).drop s.off).take w := by
        rw [hJ.ent, hJ.msg]
        exact msg_bytes hdrop (by simp only [pendAB] at hb ⊢; (clear * - hb; omega)) hpo
          (by simp only [pendAB]; (clear * -; omega))
      have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw (k' (eOfBytes (((blb π).drop s.off).take w)))
          (traceBytesB tr) { rs with msg := rs.msg + w } (ri + 1) = (some a, rs', ri') := by
        simp only [ivpWB, hw0, hval] at hiv; exact hiv
      have h24 : s.off + w ≤ π.size := by (clear * - hb; omega)
      have hT : (((blb π).drop s.off).take w).length = w := take_drop_blb h24
      have hJ' : J S π tr { s with off := s.off + w } st (buf ++ ((blb π).drop s.off).take w) caps
          ((blb π).drop (s.off + w)) { rs with msg := rs.msg + w } i cr := by
        refine ⟨hJ.st, by simp only; (clear * - hpo; omega), by simp only; (clear * - h24; omega), ?_, rfl, hJ.ent,
          ?_, hJ.caps⟩
        · simp only; rw [hJ.buf, buf_ext _ hpo]
        · simp only; rw [hJ.msg]; (clear * - hpo; omega)
      obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
        simWB hdecE hchal hdecK hcap hocc L hc as (k' _) pp Q _ t st _ caps _ i cr hs np k a rs' (ri + 1) ri' (hF' _)
          (by simp only; rw [show s.off + w - s.pend = s.off - s.pend + w by (clear * - hpo; omega)]; exact hst')
          hJ' hpos hpl hpk hk hd' hw' hiv'
      refine ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; simp only [statA]; (clear * -; omega),
        h5, fun kS ↦ ?_⟩
      have hlen : ¬ (fillA p (blb π) (.rdw w :: as) s.off wv).length < w := by
        rw [fillA, List.length_append, hT]; (clear * -; omega)
      simp only [runKW, hw0, hlen, ↓reduceIte, hdecE]
      rw [show fillA p (blb π) (.rdw w :: as) s.off wv = ((blb π).drop s.off).take w ++ fillA p (blb π) as (s.off + w) wv
        from rfl, List.take_left' hT, List.drop_left' hT]
      exact h6 kS
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .cap c r :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl,
      hpk, hk, hd, hw, hiv => by
    cases P with
    | commit ht w k' =>
      obtain ⟨-, hshp, hF'⟩ := hF
      have hpo := hJ.pend
      simp only [stAB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hst
      obtain ⟨⟨⟨hidx, hnot⟩, hcs⟩, hst'⟩ := hst
      have hnot' : r ∉ cr := by simpa using hnot
      have hco : Lvm.ASM.capOfB ht w = p.capSendBits r.lv c := by rw [hcs, hshp]
      have hd' : (driveAtomsB p π as
          { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ p.capSendBits r.lv c } t k).runSeq
          (tr.drop i) = some true := hd
      have hb := bound_of_driveB hk hd'
      simp only at hb
      have hcb : S.capBytes ht w = nodeBytes * 2 ^ p.capSendBits r.lv c := by
        rw [Scheme.capBytes, hcap, hco]; rfl
      have hoff : s.off + nodeBytes * 2 ^ p.capSendBits r.lv c ≤ π.size := by (clear * - hb; omega)
      have hT : (((blb π).drop s.off).take (S.capBytes ht w)).length = S.capBytes ht w := by
        rw [hcb]; exact take_drop_blb hoff
      have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw k' (traceBytesB tr)
          { rs with msg := rs.msg + nodeBytes * 2 ^ p.capSendBits r.lv c } ri = (some a, rs', ri') := by
        simp only [ivpWB, hco] at hiv; exact hiv
      have hJ' : J S π tr
          { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ p.capSendBits r.lv c } st (buf ++ ((blb π).drop s.off).take (S.capBytes ht w)) (caps ++ [S.capI ht w ((blb π).drop s.off)])
          ((blb π).drop (s.off + nodeBytes * 2 ^ p.capSendBits r.lv c))
          { rs with msg := rs.msg + nodeBytes * 2 ^ p.capSendBits r.lv c } i (cr ++ [r]) := by
        refine ⟨hJ.st, by simp only; (clear * - hpo; omega), by simp only; (clear * - hoff; omega), ?_, rfl, hJ.ent, ?_,
          ?_⟩
        · simp only; rw [hcb, hJ.buf, buf_ext _ hpo]
        · simp only; rw [hJ.msg]; (clear * - hpo; omega)
        · obtain ⟨offs, hlen, hdc, hcs', hix, hnd⟩ := hJ.caps
          refine ⟨offs ++ [s.off], by simp [hlen], ?_, ?_, ?_, ?_⟩
          · simp only; rw [hdc, List.zip_append hlen.symm]; simp
          · rw [hcs', List.zip_append hlen.symm, List.map_append]
            simp [hshp]
          · intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_or_ge j cr.length with hj' | hj'
            · rw [List.getElem_append_left hj']; exact hix j hj'
            · rw [List.getElem_append_right (by (clear * - hj'; omega))]
              simp only [show j - cr.length = 0 by (clear * - hlen hj hj'; omega), List.getElem_singleton]
              (clear * - hidx hlen hj hj'; omega)
          · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton r, by
              intro a ha b hb; rw [List.mem_singleton] at hb; rw [hb]; intro hab; rw [hab] at ha; exact hnot' ha⟩
      obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
        simWB hdecE hchal hdecK hcap hocc L hc as k' pp Q _ t st _ _ _ i (cr ++ [r]) hs np k a rs' ri ri' hF'
          (by simp only; rw [show s.off + nodeBytes * 2 ^ p.capSendBits r.lv c - s.pend =
            s.off - s.pend + nodeBytes * 2 ^ p.capSendBits r.lv c by (clear * - hpo; omega)]; exact hst')
          hJ' hpos hpl hpk hk hd' hw hiv'
      refine ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; simp only [statA]; (clear * -; omega),
        h5, fun kS ↦ ?_⟩
      have hfill : fillA p (blb π) (.cap c r :: as) s.off wv = ((blb π).drop s.off).take (S.capBytes ht w) ++
          fillA p (blb π) as (s.off + nodeBytes * 2 ^ p.capSendBits r.lv c) wv := by rw [hcb]; rfl
      have hlen : ¬ (fillA p (blb π) (.cap c r :: as) s.off wv).length < S.capBytes ht w := by
        rw [hfill, List.length_append, hT]; (clear * -; omega)
      simp only [runKW, hlen, ↓reduceIte]
      rw [hfill, List.take_left' hT, List.drop_left' hT, capI_fill S ht w _ _ hT]
      exact h6 kS
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .sm :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl, hpk,
      hk, hd, hw, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as pp Q := hF
      simp only [stAB, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtomsB, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } ri = (some a, rs', ri') := by
        simp only [ivpWB, hans] at hiv; exact hiv
      obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
        simWB hdecE hchal hdecK hcap hocc L hc as (k' _) pp Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off }
          t a₀ [] caps _ (i + 1) cr hs np k a rs' ri ri' (hF' _)
          (by show stAB p occ as (s.off - s.off) cr hs np = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl) hpos hpl hpk hk (by rw [hrest]; exact hd') hw hiv'
      refine ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; rfl, h5, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runKW, hle, ↓reduceIte, hq, hchal]
      rw [runLog_query_ans (ans_of_drop hc hdrop)]
      exact h6 kS
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .pclr :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl,
      hpk, hk, hd, hw, hiv => by
    rw [fol_pclr] at hF
    obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
      simWB hdecE hchal hdecK hcap hocc L hc as P [] Q { s with pos := [] } t st buf caps rs i cr [] 0 k a rs' ri ri'
        hF hst ⟨hJ.1, hJ.2, hJ.3, hJ.4, hJ.5, hJ.6, hJ.7, hJ.8⟩ rfl rfl (fun _ h ↦ by simp at h) hk hd hw hiv
    exact ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; rfl, h5, h6⟩
  | .ps h n :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl,
      hpk, hk, hd, hw, hiv => by
    cases P with
    | sample k' =>
      have hF' : ∀ y, Fol capS shpS idxS (k' y) as
          (pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat y)) Q := hF
      simp only [stAB, Bool.and_eq_true, decide_eq_true_eq] at hst
      obtain ⟨hcap32, hst'⟩ := hst
      rw [driveAtomsB, fsQuery] at hd
      obtain ⟨a₀, rest, hdrop, hd'⟩ := ask_run hd
      obtain ⟨hq, hbl⟩ := hJ.fsQ
      obtain ⟨hans, hrest, hJ1⟩ := hJ.fs hdrop
      have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw (k' (chalOf a₀)) (traceBytesB tr)
          { rs with ent := rs.ent + 72 + rs.msg, msg := 0 } ri = (some a, rs', ri') := by
        simp only [ivpWB, hans] at hiv; exact hiv
      have hpos' : (pp ++ chunk h n (answerBits a₀)) =
          pp ++ chunk h n (LeanVM.Protocol.Verifier.eToNat (chalOf a₀)) := by rw [answerBits_eq]
      obtain ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, h4, h5, h6⟩ :=
        simWB hdecE hchal hdecK hcap hocc L hc as (k' _) _ Q
          { s with log := (digestBytes s.st ++ π.extract s.pend s.off, a₀) :: s.log, st := a₀, pend := s.off,
                   pos := s.pos ++ chunk h n (answerBits a₀) }
          t a₀ [] caps _ (i + 1) cr (h :: hs) (np + n) k a rs' ri ri' (hF' _)
          (by show stAB p occ as (s.off - s.off) cr (h :: hs) (np + n) = true; rw [Nat.sub_self]; exact hst')
          (hJ1 _ rfl rfl rfl rfl)
          (by show s.pos ++ chunk h n (answerBits a₀) = _; rw [hpos, ← hpos'])
          (by rw [List.length_append, hpl]; simp [chunk]) (by
            intro q hq'
            rcases List.mem_append.mp hq' with hq'' | hq''
            · obtain ⟨h', hh', hlt⟩ := hpk q hq''
              exact ⟨h', List.mem_cons_of_mem _ hh', hlt⟩
            · refine ⟨h, List.mem_cons_self, ?_⟩
              obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq''
              exact Nat.mod_lt _ (Nat.two_pow_pos _)) hk
          (by rw [hrest]; exact hd') hw hiv'
      refine ⟨wv, s', t', st', buf', caps', i', cr', h1, h2, h3, by rw [h4]; rfl, h5, fun kS ↦ ?_⟩
      have hle : 32 + buf.length ≤ queryCap := by rw [hbl]; exact hcap32
      simp only [runKW, hle, ↓reduceIte, hq, hchal]
      rw [runLog_query_ans (ans_of_drop hc hdrop)]
      exact h6 kS
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])
  | .op r :: as, α, P, pp, Q, s, t, st, buf, caps, rs, i, cr, hs, np, k, a, rs', ri, ri', hF, hst, hJ, hpos, hpl,
      hpk, hk, hd, hw, hiv => by
    cases P with
    | query ix ps k' =>
      obtain ⟨hix, hps, hF'⟩ := hF
      subst hix hps
      have hpo := hJ.pend
      simp only [stAB, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at hst
      obtain ⟨⟨⟨⟨⟨hp0, hrc⟩, hgeo⟩, hhs⟩, hnp⟩, hst'⟩ := hst
      have hoffp : s.off = s.pend := by (clear * - hpo hp0; omega)
      simp only [geomOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgeo
      obtain ⟨⟨⟨⟨⟨-, hrow⟩, hpath⟩, hcapL⟩, hsend⟩, hcle⟩ := hgeo
      obtain ⟨capOff, hco, hcaps⟩ := capsJ_lookup hJ.caps hrc
      set ht := (shpS (idxS r)).1 with hhtdef
      set wd := (shpS (idxS r)).2 with hwddef
      set c' := p.capSendBits r.lv (p.level r).cap with hc'def
      have hcS : capS ht wd ≤ ht := capS_le (idxS r)
      have hplen : s.pos.length = (p.level r).t := by rw [hpos, hpl, hnp]
      simp only [driveAtomsB, capOffset, hco] at hd
      split at hd
      · have hk'' : ∀ (s' : DSt) (t' n : ℕ), ((fun s t ↦ driveAtomsB p π as { s with pend := s.off } t k) s' t').runSeq
            (tr.drop n) = some true → s'.off ≤ π.size := fun s' t' n h ↦ by
          have := bound_of_driveB hk h; simp only at this; (clear * - this; omega)
        have hlt : ∀ q ∈ s.pos, q < 2 ^ ht := by
          intro q hq
          obtain ⟨h', hh', hlt⟩ := hpk q (hpos ▸ hq)
          have := hhs h' hh'
          rw [this] at hlt; exact hlt
        obtain ⟨s', t', n, h1, hoff1, hst1, hpe1, hca1, hpo1, hent1, w0, hw0, hspec⟩ :=
          openLoopB_sim S π L tr hc hdecK (p.level r) c' capOff ht wd (by rw [hrow, hocc])
            (by rw [hpath, hcapL]; (clear * - hcS; omega)) (by rw [hsend, hcapL]; exact hcle)
            (by rw [hcap, hsend]) s t i _ hlt hk'' hd
        have hoff' : s'.off ≤ π.size := hk'' s' t' (i + n) h1
        set rows := (opRows (traceBytesB tr) wd (S.occ ht wd) (p.level r).path s.pos.length (entOff tr i)).1
        have hiv' : ivpWB Lvm.ASM.capOfB occ shpS pthB hqB S.rw (k' rows) (traceBytesB tr)
            { rs with ent := entOff tr (i + n) } ri = (some a, rs', ri') := by
          simp only [ivpWB] at hiv
          rw [show pthB (idxS r) = (p.level r).path by rw [pthB, hpath],
            show hqB (idxS r) = 2 ^ (p.level r).cap - 2 ^ c' by rw [hqB, hcapL, hsend],
            ← hpos, show occ ht wd = S.occ ht wd by rw [hocc], hJ.ent, hent1] at hiv
          exact hiv
        have hJ' : J S π tr { s' with pend := s'.off } st [] caps ((blb π).drop s'.off)
            { rs with ent := entOff tr (i + n) } (i + n) cr := by
          refine ⟨by rw [hJ.st]; exact hst1.symm, le_rfl, hoff', by simp, rfl, rfl, ?_, ?_⟩
          · show rs.msg = s'.off - s'.off; rw [hJ.msg, hoffp]; simp
          · show CapsJ S π caps s'.caps cr; rw [hca1]; exact hJ.caps
        obtain ⟨wr, s'', t'', st', buf', caps', i', cr', h2, h3, h4, h5, h6, h7⟩ :=
          simWB hdecE hchal hdecK hcap hocc L hc as (k' rows) ps Q { s' with pend := s'.off } t' st [] caps _
            (i + n) cr hs np k a rs' ri ri' (hF' rows)
            (by show stAB p occ as (s'.off - s'.off) cr hs np = true; rw [Nat.sub_self]; exact hst')
            hJ' (by show s'.pos = ps; rw [hpo1, hpos]) hpl hpk hk h1 hw hiv'
        refine ⟨w0 ++ wr, s'', t'', st', buf', caps', i', cr', h2, h3, h4, ?_, ?_, fun kS ↦ ?_⟩
        · rw [h5]; show s'.off + statA p as = _
          rw [hoff1, hplen]; simp only [statA, nodeBytes]; (clear * -; ring)
        · rw [List.length_append, hw0, h6, hplen]; simp only [expA, nodeBytes]; rfl
        have hbuf : buf = [] := by rw [hJ.buf, hoffp]; simp
        have hfill : fillA p (blb π) (.op r :: as) s.off (w0 ++ wr) =
            fillPaths (blb π) ((p.level r).row + 32 * (p.level r).path) (32 * ((p.level r).cap - c'))
              s.pos.length s.off w0 ++ fillA p (blb π) as s'.off wr := by
          rw [fillA, ← hc'def, hoff1, hplen, show nodeBytes = 32 from rfl, fillPaths_append _ _ _ _ _ _ _
            (by rw [hw0, hplen]), List.drop_left' (by rw [hw0, hplen])]
        simp only [runKW, hcaps]
        rw [hfill, runLog_bind, ← hpos, hspec, Option.bind_some, hbuf]
        exact h7 kS
      · exact absurd (runSeq_ret_true hd).2 (by simp)
    | fail => simp [ivpWB] at hiv
    | _ => exact absurd hF (by simp [Fol])

end Main

/-! ## `parseOkB`: the size, the header, the statement check -/

theorem parseOkB_partsS {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOkB p vk c π = true) :
    piStatic p ≤ π.size ∧ π.get! 0 = 0x53 ∧ zeroBytes π 1 7 = true ∧
      ((Header.ofProof π).b = 0 ∨ (Header.ofProof π).b = 1) ∧ (Header.ofProof π).vk = vk ∧
      1 ≤ (Header.ofProof π).n ∧ (Header.ofProof π).n ≤ chainCap ∧ c = (Header.ofProof π).stmt := by
  simp only [parseOkB, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, -, h0, hz, hb, hvk, hn1, hn2, -, hif⟩ := h
  refine ⟨hs, h0, hz, hb, hvk, hn1, hn2, ?_⟩
  by_cases hb0 : (Header.ofProof π).b = 0
  · simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
    exact hif.2
  · simp only [hb0, ↓reduceIte, beq_iff_eq] at hif
    exact hif

theorem okSL_of_parseOkB {p : Params} {vk c : Digest} {π : ByteArray} (h : parseOkB p vk c π = true) {hb : ℕ}
    (hH : hdrFixS ≤ hb) : Lvm.ASM.okSL vk c (xOfH hb π) = true := by
  obtain ⟨-, -, -, hb, hvk, hn1, hn2, hc⟩ := parseOkB_partsS h
  obtain ⟨eb, evk, ecL, -, en, eh⟩ := hdrOf_xOfH_fix π hH
  unfold Lvm.ASM.okSL
  dsimp only
  rw [eb, evk, ecL, en, eh]
  unfold Header.stmt Header.leaf at hc
  rw [leafStmtF_eq, nodeStmtF_eq] at hc
  generalize Header.ofProof π = hd at *
  rcases hb with hb | hb
  · simp only [hb, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]
  · simp only [hb, one_ne_zero, ↓reduceIte] at hc
    simp [hb, hvk, hn1, hn2, hc]

/-- **V_S at S2GB ⇒ the compiled verifier on the expanded proof** (on logs). -/
theorem refinesB_of (PS : List UInt8 → VerifierProgram Bool) (nR : ℕ)
    (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (prog : RecursionFast.Digest → RecursionFast.Digest → DM Acc) (φ : Acc → Prop)
    (Pre : ByteArray → RecursionFast.Digest → RecursionFast.Digest → List UInt8 → Prop)
    (hD : ∀ vk c sig, D vk c sig = true →
      (runD (prog vk c) sig (RS.startH (headerBytesP P20B))).2.ok = true ∧
        φ (runD (prog vk c) sig (RS.startH (headerBytesP P20B))).1)
    (hPre : ∀ vk c π sig, parseOkB P20B vk c π = true →
      (∀ t < headerBytesP P20B - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      Pre sig vk c (xOfH (headerBytesP P20B) π))
    (href : ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), Pre sig vk c x →
      RefAtPWB capOfB occOfU shpS pthB hqB rwB20 sig 0 (prog vk c) (PS x) (fun _ b ↦ b = true) φ nR)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf P20B (schedule P20B)) [] fun _ _ ↦ True) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      (if parseOkB P20B vk c π then driveB P20B π (D vk c) else .ret false).runLog L = some true →
      ∃ w : List UInt8, ((schemeSWB fmtB20 vk PS).V c (fillB P20B π w)).runLog L = some true := by
  intro vk L c π h
  by_cases hp : parseOkB P20B vk c π = true
  swap
  · simp [hp, OProg.runLog] at h
  simp only [hp, ↓reduceIte] at h
  obtain ⟨tr, hrs, hc⟩ : ∃ tr, (driveB P20B π (D vk c)).runSeq tr = some true ∧ LogCons L tr :=
    ⟨_, runSeq_traceOf L _ h, logCons_traceOf L _⟩
  obtain ⟨hlo, h0, hz, -⟩ := parseOkB_partsS hp
  have h8 := eight_le_P P20B
  have hbS : headerBytesP P20B ≤ piStatic P20B := headerBytesP_le_piSize P20B
  have hHle : headerBytesP P20B ≤ π.size := le_trans hbS hlo
  -- the driver: q₀, the seed, the schedule
  unfold driveB at hrs
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons hrs
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItemsB_eq] at h2
  obtain ⟨sf, tf, n, hf1, hf2, -, -⟩ := drive_runB _ π _ _ _ _ rest h2
  obtain ⟨hnil, hbf⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hbf
  obtain ⟨-, hF⟩ := hbf
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  set hb := headerBytesP P20B with hbdef
  have hlog : streamOf sf.log = traceBytesB ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest with htr
  set x := xOfH hb π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpre : Pre (traceBytesB tr) vk c x := hPre vk c π _ hp (seed_bytesH π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := hD vk c _ hF
  obtain ⟨b, hb1, -, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpre (RS.startH hb) hok0 hacc
  obtain ⟨⟨o, rs', nW⟩, hW⟩ : ∃ r, ivpWB capOfB occOfU shpS pthB hqB rwB20 (PS x) (traceBytesB tr)
      (RS.startH hb) 0 = r := ⟨_, rfl⟩
  rw [hW] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  set S : Scheme := schemeSWB fmtB20 vk PS with hSdef
  have hJ0 : J S π tr ⟨hb, hb, st₀, [(seedQuery π a₀ hb, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((blb π).drop hb) (RS.startH hb) 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_twoH π a₀ st₀ rest h8 hHle).symm,
      by show 0 = hb - hb; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  have hw : WAt S.rw 0 (widthsA (atomsOf P20B (schedule P20B))) := by
    rw [← readWidthsP_eqAP]; exact wAt_getD _ _
  obtain ⟨w, s', t', st', buf', caps', i', cr', -, hk', -, hoff', hwl, hrun⟩ :=
    simWB (S := S) (π := π) (tr := tr) (p := P20B) rfl rfl rfl rfl (occ := occOfU) rfl L hc
      (atomsOf P20B (schedule P20B)) (PS x) [] _ _ (piStatic P20B) st₀ [] [] (RS.startH hb) 2 [] [] 0 _ true rs'
      0 nW (hfol x) (by rw [Nat.sub_self]; exact stAB_P20B) hJ0 rfl rfl (fun _ h ↦ by simp at h)
      (fun s'' t'' m hm ↦ by
        obtain ⟨-, hbb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hbb
        rw [hbb.1.1]; exact hlo)
      h2 hw hW
  obtain ⟨-, hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hstat : hb + statA P20B (atomsOf P20B (schedule P20B)) = piStatic P20B := by
    rw [← hb'.1.1, hoff']
  refine ⟨w, ?_⟩
  -- the expanded proof
  have hlb : (blb π).length = π.size := length_blb π
  have hbl : (fillA P20B (blb π) (atomsOf P20B (schedule P20B)) hb w).length =
      statA P20B (atomsOf P20B (schedule P20B)) + expA P20B (atomsOf P20B (schedule P20B)) :=
    length_fillA _ _ _ _ _ (by rw [hlb, hstat]; exact hlo) hwl
  have htk : ((blb π).take hb).length = hb := by
    rw [List.length_take, hlb]; exact Nat.min_eq_left hHle
  have hdata : (fillB P20B π w).data.toList =
      (blb π).take hb ++ fillA P20B (blb π) (atomsOf P20B (schedule P20B)) hb w := by
    rw [← fillItems_eq]; rfl
  have hsz : (fillB P20B π w).size = pzB P20B := by
    rw [← length_blb, show blb (fillB P20B π w) = (fillB P20B π w).data.toList from rfl, hdata,
      List.length_append, htk, hbl, pzB, expandBytes_eq]
    (clear * - hstat; omega)
  have hx' : ((fillB P20B π w).data.toList.drop 8).take (hb - 8) = x := by
    rw [hdata, List.drop_append_of_le_length (by rw [htk]; exact h8),
      List.take_left' (by rw [List.length_drop, htk]), hx, xOfH, List.drop_take]
  have hpref : (fillB P20B π w).data.toList.take 8 = Lvm.ASM.sPrefix := by
    rw [hdata, List.take_append_of_le_length (by rw [htk]; exact h8), List.take_take, Nat.min_eq_left h8]
    exact take8_of_parse' (le_trans h8 hHle) h0 hz
  have hbd : (fillB P20B π w).data.toList.drop hb = fillA P20B (blb π) (atomsOf P20B (schedule P20B)) hb w := by
    rw [hdata, List.drop_left' htk]
  have hS_hdr : S.hdr (fillB P20B π w) = some (x, fillA P20B (blb π) (atomsOf P20B (schedule P20B)) hb w) := by
    show Lvm.ASM.hdrSW (pzB P20B) hb (fillB P20B π w) = _
    rw [Lvm.ASM.hdrSW, if_pos ⟨hsz, hpref⟩, hx', hbd]
  have hqc : 32 + x.length ≤ queryCap := by
    rw [hx, length_xOfH π hHle]; decide
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okSL vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [okSL_of_parseOkB hp (hdrFixS_le_P _)]
    simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, runLog_query_ans (ans_of_drop (q := q0Query) (a := a₀) hc (i := 0) rfl),
    show S.seedQ a₀ x = seedQuery π a₀ hb from toQ_seedH π a₀ hb,
    runLog_query_ans (ans_of_drop (q := seedQuery π a₀ hb) (a := st₀) hc (i := 1) rfl),
    show S.P x = PS x from rfl, runW_eq_runKW, hrun]
  rfl

end Lvm.VEq
