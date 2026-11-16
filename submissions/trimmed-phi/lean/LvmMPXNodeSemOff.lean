/- `LvmMPXNodeSemOff` (GOLF2 off-path move, group 24 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXRead2, LvmXRead1Defs, LvmXRead1, LvmMPXNodeSem,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXRead2
import LvmXRead1Defs
import LvmXRead1
import LvmMPXNodeSem
import LvmMPXReadOff
import LvmXTopOff
import LvmJBMutual
import LvmMlListLemmas

-- ===== from `LvmXRead2` =====

section
section
namespace Lvm.X
open RecursionFast

theorem crOcc_le : crOcc ≤ 64 := by decide

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- **The word the decoder consumes** (`LvmXDec`'s `wd`): row word `t` at position `p`. -/
def readWd (L : Log) (cap : List Digest) (p t : ℕ) : BF64 := (readRow L cap p).getD t 0

theorem decLE_nil : decLE [] = 0 := rfl

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- Word `t < 64` of the row: zero below `64 − crOcc`, else leaf word `t − (64 − crOcc)`. -/
theorem readRow_getD (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    (readRow L cap p).getD t 0 = if t < 64 - crOcc then 0 else
      decLE ((((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc)))).take 8) := by
  have hc := crOcc_le
  rw [List.getD_eq_getElem _ _ (by rw [readRow_length]; exact ht)]
  simp only [readRow, xRowOf]
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp only [List.length_replicate] at h1; (clear * - h2 h1; omega)
  · simp only [List.length_replicate] at h1; omega
  · simp

theorem decLE_zeros : decLE (List.replicate 8 0) = 0 := by decide

/-- **The row is `Scheme.padRow`'s term** at `wd = 64`, `occ = crOcc`: the leaf's bytes after
`8 · (64 − crOcc)` zero bytes, read as 64 words. -/
theorem readRow_pad (L : Log) (cap : List Digest) (p : ℕ) :
    readRow L cap p =
      xRowOf decLE 64 (List.replicate (8 * (64 - crOcc)) 0 ++ (xLeafBytes L cap p).getD []) := by
  have hc := crOcc_le
  apply List.ext_getElem (by simp [xRowOf])
  intro t h1 h2
  have ht : t < 64 := by simpa [xRowOf] using h2
  rw [← List.getD_eq_getElem _ 0 h1, readRow_getD L cap p ht]
  simp only [xRowOf, List.getElem_map, List.getElem_range]
  split_ifs with h
  · rw [List.drop_append_of_le_length (by simp only [List.length_replicate]; (clear * - h; omega)),
      List.take_append_of_le_length (by simp only [List.length_drop, List.length_replicate]; (clear * - h; omega)),
      List.drop_replicate, List.take_replicate, Nat.min_eq_left (by (clear * - h; omega))]
    exact decLE_zeros.symm
  · have hd : (List.replicate (8 * (64 - crOcc)) (0 : UInt8) ++ (xLeafBytes L cap p).getD []).drop
        (8 * t) = ((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc))) := by
      rw [List.drop_append, List.drop_replicate, Nat.sub_eq_zero_of_le (by (clear * - h; omega)),
        List.replicate_zero, List.nil_append, List.length_replicate,
        show 8 * t - 8 * (64 - crOcc) = 8 * (t - (64 - crOcc)) by (clear * - h; omega)]
    rw [hd]

/-- **An erasure reads as 64 zero words.** -/
theorem readRow_erasure {L : Log} {cap : List Digest} {p : ℕ} (h : xLeafBytes L cap p = none) :
    readRow L cap p = List.replicate 64 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_replicate, ← List.getD_eq_getElem _ 0 h1,
    readRow_getD L cap p (by simpa using h2), h]
  split_ifs
  · rfl
  · simp [decLE_nil]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- The reading under a cap node `d0`: 8 steps down to the leaf digest, then the leaf's bytes. -/
def crRd (L : Log) (d0 : Digest) (p : ℕ) : Option (List UInt8) :=
  (xDescend L 8 d0 p).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- On a position of the tree, the leaf bytes are the reading under its cap node. -/
theorem xLeafBytes_eq {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ 15)
    (hpc : p / 256 < cap.length) :
    xLeafBytes L cap p = crRd L (cap[p / 256]'hpc) p := by
  unfold xLeafBytes crRd
  rw [Nat.mod_eq_of_lt hp, show (2 : ℕ) ^ (15 - 7) = 256 from rfl, List.getElem?_eq_getElem hpc]
  all_goals rfl

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- **The copied leaf word as a `K` element is the row's word `64 − crOcc + t`.** -/
theorem crLeafW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < crOcc) :
    wK (crLeafW (xLeafBytes L cap p) t) = (readRow L cap p).getD (64 - crOcc + t) 0 := by
  have hc := crOcc_le
  rw [wK_crLeafW, readRow_getD L cap p (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **Row word `t` of a reading** as the machine stores it: `64 − crOcc` zero words, then the
leaf words `0 … crOcc − 1`. -/
def crRowW (o : Option (List UInt8)) (t : ℕ) : Word :=
  if t < 64 - crOcc then 0 else crLeafW o (t - (64 - crOcc))

theorem crRowW_none (t : ℕ) : crRowW none t = 0 := by
  simp [crRowW, crLeafW_none]

/-- **The stored word as a `K` element is the row's word.** -/
theorem crRowW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    wK (crRowW (xLeafBytes L cap p) t) = (readRow L cap p).getD t 0 := by
  rw [readRow_getD L cap p ht, crRowW]
  split_ifs
  · rfl
  · rw [wK_crLeafW]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`; every other
cell below `regs` is kept (`frame`). -/
theorem readIR_nw (bX pL capW wB : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) : ¬ Writes (readIR bX pL capW wB) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopy, crZero, crZeroBody, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA,
    crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  (clear * - h; omega)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast

/-- Loop bounds hold on every tape (no `loopT`). -/
theorem safe_readIR (I : Array Word) (t bX pL capW wB : ℕ) : Safe I t (readIR bX pL capW wB) :=
  safe_of_noLoopT (noLoopT_readIR bX pL capW wB)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- **The cap node's words**: after `crCapPs ; crLd4`, `rQ0 … rQ3` hold `cap[p / 256]`. -/
theorem cr_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW : ℕ} {cap : List Digest}
    (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 256 < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M rQ3] =
      packBytes (cap[p / 256]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (crCapPs capW)) := by simp +decide only [crCapPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR I (.blk (crCapPs capW)) s).M crTA = toWord (capW + 4 * (p / 256)) := by
    simp only [crCapPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, show (8 : Word) = toWord 8 from rfl, shr_toWord (by (clear * - hp; omega)) (by norm_num),
      show (2 : Word) = toWord 2 from rfl, shl_toWord (by norm_num) (by (clear * - hcw he; omega)), add_toWord]
    congr 1
    (clear * -; omega)
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by (clear * - hcw he; omega)) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- **The walk's state at height `h`**: either every entry so far was found and `rQ0 … rQ3`
hold a digest `d` whose descent from height `h` is the descent from the cap node `d₀`, or an
entry was missing (or of another length) and the descent from `d₀` is `none`. -/
def crWalk (L : Log) (d0 : Digest) (p h : ℕ) (M : Mem) : Prop :=
  (rd M crOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    xDescend L 8 d0 p = xDescend L h d p) ∨
  (rd M crOk = 0 ∧ xDescend L 8 d0 p = none)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- What the copy stores at row cell `i`: `0` in the first `64 − crOcc` cells, then copy word
`i − (64 − crOcc)`. -/
def crCpRow (I : Array Word) (x : Word) (ql i : ℕ) : Word :=
  if i < 64 - crOcc then 0 else crCpW I x ql (i - (64 - crOcc))

/-- **A copy of the leaf's words is a copy of its row** (`crRowW`). -/
theorem crCpRow_of {I : Array Word} {x : Word} {ql : ℕ} {o : Option (List UInt8)}
    (h : ∀ t, crCpW I x ql t = crLeafW o t) (i : ℕ) : crCpRow I x ql i = crRowW o i := by
  rw [crCpRow, crRowW]
  split_ifs
  · rfl
  · exact h _

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Read
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}

theorem cr_lo_get : Lo (crGet bX) := by
  simp +decide [crGet, Lo, Prim.dst, regs, crK, crAd, crX, crQn, and_true]

end Read
end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Read
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One node step keeps the walk's state**, one level down. -/
theorem cr_nodeWalk (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p h : ℕ}
    (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hW : crWalk L d0 p (h + 1) s.M) :
    crWalk L d0 p h (semXIR (crTape c π L) (crNode bX pL) s).M := by
  rcases hW with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · obtain ⟨n1, n2⟩ := cr_node_sem hbX hbX2 hpL hD hX s hM hXs hp hh hP hH hOk hT
    rw [xDescend_succ L h d p] at hc
    cases hn : xStep L p h d with
    | none =>
      rw [hn] at hc
      exact .inr ⟨n2 hn, hc⟩
    | some d' =>
      rw [hn] at hc
      obtain ⟨o1, o2⟩ := n1 d' hn
      exact .inl ⟨o1, d', o2, hc⟩
  · have e : semXIR (crTape c π L) (crNode bX pL) s = s := by
      rw [crNode, semXIR_ite, hOk, if_pos rfl]; rfl
    rw [e]; exact .inr ⟨hOk, hc⟩

/-- **The height loop**: `m` node steps from height `m` reach height `0`; the heap, `crP` and
`crWA` are kept. -/
theorem cr_nodeLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {d0 : Digest} {p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M crP = toWord p → rd s.M crHc = toWord m → crWalk L d0 p m s.M →
      crWalk L d0 p 0 (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      Inv (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crP = rd s.M crP ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crWA = rd s.M crWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := crTape c π L
    have h1 := cr_nodeWalk hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (cr_wf_node (bX := bX) (pL := pL)) hM
    have hH1 := hframeK I (crNode bX pL) s cr_loK_node
    have fr : ∀ r, (r = crP ∨ r = crWA ∨ r = crHc) →
        rd (semXIR I (crNode bX pL) s).M r = rd s.M r :=
      fun r hr => frame I _ s (cr_wf_node (bX := bX) (pL := pL)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (cr_node_nw hr)
    have hM' : Inv (decS crHc (semXIR I (crNode bX pL) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS crHc (semXIR I (crNode bX pL) s)).M crHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by omega)
    have dk : ∀ r, r ≠ crHc → rd (decS crHc (semXIR I (crNode bX pL) s)).M r =
        rd (semXIR I (crNode bX pL) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : crWalk L d0 p m (decS crHc (semXIR I (crNode bX pL) s)).M := by
      unfold crWalk at h1 ⊢
      rw [dk crOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS crHc (semXIR I (crNode bX pL) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [crHc, regs] at *; omega)).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := cr_nodeLoop hD hX hp m _ (by omega) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `crLeaf`, `crX` and `crQe` are such that the copy stores the leaf words of
the reading under the cap node `d₀` (`crLeafW`, zeros for an erasure). -/
theorem cr_leaf_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {d0 : Digest} {p : ℕ}
    (hW : crWalk L d0 p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crQe = toWord ql ∧
      ∀ t, crCpW (crTape c π L) (rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crX) ql t =
        crLeafW (crRd L d0 p) t := by
  set I := crTape c π L with hI
  have hs := hM.1
  simp only [regs] at hs
  rw [crLeaf, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const crQe 0]) (by simp +decide only [WF, Prim.dst, crQe]) hM
  have hQ0 : rd (semXIR I (.blk [.const crQe 0]) s).M crQe = toWord 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [crQe]; (clear * - hs; omega))
  have fr0 : ∀ r, r ≠ crQe → rd (semXIR I (.blk [.const crQe 0]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  have hXs0 : ∀ a < L.length, rd (semXIR I (.blk [.const crQe 0]) s).M (bX + a) = Xi a :=
    fun a ha => by rw [fr0 _ (by simp only [crQe, regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a ha]
  have hW0 : crWalk L d0 p 0 (semXIR I (.blk [.const crQe 0]) s).M := by
    unfold crWalk at hW ⊢
    rw [fr0 crOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const crQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq]
    have hrd : crRd L d0 p = (xFindA L d).map fun e => xQb e.1 := by
      rw [crRd, hc]; rfl
    rw [hrd]
    obtain ⟨lk1, lk2, lk3, lk4, lk5⟩ := cr_look_spec hbX hbX2 hpL hD hX s0 hM0 hXs0 d hT
    have hQ1 := (lk5 crQe (by decide) (by decide)).trans hQ0
    generalize semXIR I (lookIR4 bX pL) s0 = s1 at lk1 lk2 lk3 lk4 hQ1
    have hs1 := lk4.1
    simp only [regs] at hs1
    rw [semXIR_ite]
    cases hk : ansIdx L d with
    | none =>
      rw [lk2 hk, if_pos rfl, xFindA_none hk]
      refine ⟨0, by norm_num, hQ1, fun t => ?_⟩
      simp [crCpW_zero, crLeafW_none]
    | some k =>
      obtain ⟨b, hb, hlo, hfd, hxb⟩ := lk1 k hk
      obtain ⟨hkL, hpre⟩ := xFindA_some hk
      rw [hfd, if_neg (by decide), hpre, Option.map_some]
      have hxl := hD.posE_lt hkL
      have hsm := hD.small
      have hq := hD.hq _ (List.getElem_mem hkL)
      obtain ⟨g1, g2⟩ := cr_get_sem hbX hbX2 hpL I s1 lk4 (b := b) (x := posE4 pL L k) (by (clear * - hb hkL hsm; omega))
        (by (clear * - hkL hxl hq; omega)) hlo (by rw [lk3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2 hkL; omega)), hXs0 b hb, hxb])
      have hM2 := inv_sem I (cr_wf_get (bX := bX)) lk4
      rw [semXIR_seq]
      generalize semXIR I (crGet bX) s1 = s2 at g1 g2 hM2
      have hs2 := hM2.1
      simp only [regs] at hs2
      refine ⟨L[k].1.size, hq, ?_, fun t => ?_⟩
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [crQe]; (clear * - hkL hs2; omega)), g2, cr_tp_len hD hkL, or_self_eval]
      · have e : rd (semXIR I (.blk [.op .or crQe crQn crQn]) s2).M crX =
            toWord (posE4 pL L k) := by
          simp only [semXIR, runPrims, List.foldl, Prim.run]
          rw [rd_set_ne (by decide), g1]
        rw [e, cr_cpW_entry hD hkL t]
  · rw [hOk, if_pos rfl]
    have hrd : crRd L d0 p = none := by rw [crRd, hc]; rfl
    rw [hrd]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) crQe = _
      rw [runPrims_nil, hQ0], fun t => ?_⟩
    rw [crCpW_zero, crLeafW_none]

end Read
end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem cr_wf_zeroBody : WF crZeroBody := by
  simp +decide only [crZeroBody, WF, Prim.dst, crWA, cTmp, and_true]

theorem cr_wf_zero : WF crZero := by
  simp +decide only [crZero, crZeroBody, WF, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem cr_wf_copy : WF crCopy := by
  simp +decide only [crCopy, crZero, crZeroBody, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK,
    crWA, crTA, cr8, crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]

/-- The registers the zero prefix keeps. -/
theorem cr_zero_nw {r : ℕ} (hr : r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) :
    ¬ Writes crZero r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [crZero, crZeroBody, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, crX, crQe,
    crP, crTA, cr8, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false,
    not_or, exists_false, not_false_eq_true, and_self]

/-- **The row's zero prefix**: from `crWA = a`, cells `a … a + 63 − crOcc` get `0`; every other
heap cell is kept; `crWA` ends at `a + 64 − crOcc`. -/
theorem cr_zero_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : regs ≤ a)
    (ha2 : a + 64 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size) (hA : rd s.M crWA = toWord a) :
    (∀ i < 64 - crOcc, rd (semXIR I crZero s).M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (64 - crOcc) ≤ y) → rd (semXIR I crZero s).M y = rd s.M y) ∧
    Inv (semXIR I crZero s).M ∧ rd (semXIR I crZero s).M crWA = toWord (a + (64 - crOcc)) := by
  have hs := hM.1
  have hc := crOcc_le
  simp only [regs] at hs ha
  rw [crZero, semXIR_seq]
  have w0 : WF (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) := by
    simp +decide only [WF, Prim.dst, crV, crNw, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
      forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s
  have r0 : rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crV = 0 ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crNw =
        toWord (64 - crOcc) ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M crWA =
        toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crV, crNw, crWA]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hA
  have k0 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crNw, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  generalize semXIR I (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨v0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M crV = 0 ∧ rd s'.M crWA = toWord (a + j) ∧ (∀ i < j, rd s'.M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + j ≤ y) → rd s'.M y = rd s.M y)
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp →
      rd (entryK crCw crNw (toWord (64 - crOcc)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK crCw crNw (toWord (64 - crOcc)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun i hi => absurd hi (by (clear * - hi; omega)), fun y hy _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), v0]
    · rw [hE _ (by decide) (by decide), a0, Nat.add_zero]
    · simp only [regs] at hy
      rw [hE _ (by simp only [crCw]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)),
        k0 y (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 - crOcc → P j s' →
      P (j + 1) (decS crCw (semXIR I crZeroBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    rw [crZeroBody, semXIR_seq]
    obtain ⟨c1, c2, hM1⟩ := store_sem I s' i1 (p := crWA) (v := crV) (x := a + j) (by decide)
      (by decide) i4 (by simp only [regs]; (clear * - ha ha2; omega)) (by (clear * - ha ha2 hc hj; omega)) (by (clear * - hsz hc z0 h0 hj i2; omega))
    have z1 := size_sem I (.store crWA crV) s'
    generalize semXIR I (.store crWA crV) s' = s1 at c1 c2 hM1 z1
    have hs1 := hM1.1
    simp only [regs] at hs1
    have hdr : ∀ r, r < regs → r ≠ a + j := fun r hr => by simp only [regs] at hr; (clear * - ha ha2 hr; omega)
    have b2 : ∀ r, r ≠ crWA → rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M r = rd s1.M r :=
      fun r hr => by
        simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
    have hM2 := inv_sem I (P := .blk [.op .add crWA crWA cOne])
      (by simp +decide only [WF, Prim.dst, crWA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
        forall_eq, or_false, and_true]) hM1
    have hd : ∀ y, y ≠ crCw → rd (decS crCw (semXIR I (.blk [.op .add crWA crWA cOne]) s1)).M y =
        rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M y := fun y hy => rd_decS (Ne.symm hy) _
    have hx : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ crWA ∧ y ≠ cTmp := fun y hy => by
      simp only [regs, crCw, crWA, cTmp] at *; (clear * - hy; omega)
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, z1, i2], ?_, ?_,
      fun i hi => ?_, fun y hy hy2 => ?_⟩
    · rw [hd _ (by decide), b2 _ (by decide), c2 _ (hdr _ (by decide)) (by decide), i3]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [crWA]; (clear * - hs z0 h0 i2 z1; omega)), c2 _ (hdr _ (by decide)) (by decide), i4,
        c2 _ (hdr _ (by decide)) (by decide), show rd s'.M cOne = 1 from i1.2 0 (by decide),
        add_one_toWord, Nat.add_assoc]
    · obtain ⟨x1, x2, x3⟩ := hx (a + i) (by simp only [regs]; (clear * - ha ha2; omega))
      rw [hd _ x1, b2 _ x2]
      by_cases hij : i = j
      · subst hij; rw [c1, i3]
      · rw [c2 _ (by (clear * - hij; omega)) x3, i5 i (by (clear * - hi hij; omega))]
    · obtain ⟨x1, x2, x3⟩ := hx y hy
      rw [hd _ x1, b2 _ x2, c2 _ (by (clear * - ha ha2 hy2 x1 x2 x3; omega)) x3, i6 y hy (by (clear * - hy2 x1 x2 x3; omega))]
  have hfin := loopK_run I crZeroBody P s0 hM0 (c := crCw) (n := crNw) (K := 64 - crOcc)
    (by decide) (by decide) (by decide) n0 (by (clear * - hc; omega)) h0 hstep
  exact ⟨hfin.2.2.2.2.1, hfin.2.2.2.2.2, hfin.1, hfin.2.2.2.1⟩

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + 63` get
`crCpRow I x ql ·` (`64 − crOcc` zero words, then copy words `0 … crOcc − 1`); every other heap
cell is kept; `crWA` ends at `a + 64`. -/
theorem cr_copy_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < 64, rd (semXIR I crCopy s).M (a + i) = crCpRow I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) → rd (semXIR I crCopy s).M y = rd s.M y) ∧
    Inv (semXIR I crCopy s).M ∧ rd (semXIR I crCopy s).M crWA = toWord (a + 64) ∧
    rd (semXIR I crCopy s).M crP = rd s.M crP := by
  have hc := crOcc_le
  -- the zero prefix
  obtain ⟨z1, z2, hMz, az⟩ := cr_zero_sem I s hM ha (by (clear * - ha2; omega)) hsz hA
  have fz : ∀ r, (r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) →
      rd (semXIR I crZero s).M r = rd s.M r := fun r hr =>
    frame I _ s cr_wf_zero hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (cr_zero_nw hr)
  have hszz := size_sem I crZero s
  rw [crCopy, semXIR_seq]
  generalize semXIR I crZero s = s1 at z1 z2 hMz az fz hszz
  have hX1 : rd s1.M crX = x := (fz _ (.inl rfl)).trans hX
  have hQ1 : rd s1.M crQe = toWord ql := (fz _ (.inr (.inl rfl))).trans hQ
  have hP1 : rd s1.M crP = rd s.M crP := fz _ (.inr (.inr (.inl rfl)))
  -- the copy of `crOcc` words to `a' = a + (64 − crOcc)`
  have hs := hMz.1
  have h1 : rd s1.M cOne = 1 := hMz.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hMz
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)]) s1
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
    s1
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crNw = toWord crOcc ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crWA = toWord (a + (64 - crOcc) + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
        s1).M crP = rd s1.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ1 | exact az | (rw [hX1, h1]; all_goals rfl)
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
    s1 = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord crOcc) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord crOcc) s0.M) crCw = toWord crOcc :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord crOcc) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord crOcc) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw crOcc ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show crOcc < 2 ^ 64 by (clear * - hc; omega))]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; (clear * - hy; omega)
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I (a := a + (64 - crOcc)) (nw := crOcc) hql
    (by (clear * - ha; omega)) (by (clear * - ha2 hc; omega)) (by (clear * - hc; omega)) crOcc 0 ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hc hszz hsz0; omega)) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  have back : ∀ y, regs ≤ y → (y < a + (64 - crOcc) ∨ a + 64 ≤ y) →
      rd (iterL (semXIR I crCopyBody) crCw crOcc ⟨entryK crCw crNw (toWord crOcc) s0.M, s0.o⟩).M y =
        rd s1.M y := fun y hy1 hy2 => by
    rw [d2 y hy1 (by (clear * - hc hy2; omega))]
    show rd (entryK crCw crNw (toWord crOcc) s0.M) y = rd s1.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  refine ⟨fun i hi => ?_, fun y hy1 hy2 => ?_, d3, ?_, ?_⟩
  · rw [crCpRow]
    split_ifs with h
    · rw [back _ (by simp only [regs] at ha ⊢; (clear * - ha ha2 hi; omega)) (.inl (by (clear * - h; omega))), z1 i h]
    · rw [show a + i = a + (64 - crOcc) + (i - (64 - crOcc)) by (clear * - h; omega)]
      exact d1 _ (by (clear * -; omega)) (by (clear * - hc hi h; omega))
  · rw [back y hy1 (by (clear * - hc hy2; omega)), z2 y hy1 (by (clear * - hc hy2; omega))]
  · rw [d4, show a + (64 - crOcc) + (0 + crOcc) = a + 64 by (clear * - hc; omega)]
  · rw [d5]
    show rd (entryK crCw crNw (toWord crOcc) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0, hP1]

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Read2
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the row words of position `p` at `a … a + 63`; `crP := p + 1`,
`crWA := a + 64`; every other heap cell kept. -/
theorem cr_pos_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < 2 ^ 15) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + 64 + 2 < 2 ^ 64) (hsz : a + 64 ≤ s.M.size) :
    (∀ t < 64, rd (semXIR (crTape c π L) (crPos bX pL capW) s).M (a + t) =
      crRowW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 64 ≤ y) →
      rd (semXIR (crTape c π L) (crPos bX pL capW) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (crPos bX pL capW) s).M ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crWA = toWord (a + 64) ∧
    rd (semXIR (crTape c π L) (crPos bX pL capW) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 256 < cap.length := by rw [hcl]; omega
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, WF, Prim.dst,
    crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (crCapPs capW)) crLd4) := ⟨by simp +decide only [crCapPs, Lo, Prim.dst,
    regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true], cr_lo_ld4⟩
  have q1 := cr_capLd_sem I s hM (by rw [hcl]; omega) hcap (by omega) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (crCapPs capW)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [crCapPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3, crP,
        crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (crCapPs capW)) crLd4) s
  rw [crPos, semXIR_seq]
  generalize semXIR I (.seq (.blk (crCapPs capW)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord 8)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1).M crNH = toWord 8 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord 8)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalk L (cap[p / 256]'hpc) p 8 s2.M := by
    refine .inl ⟨o2.1, cap[p / 256]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; omega) (by simp only [crNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord 8) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord 8) s2.M) crHc = toWord 8 :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord 8) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord 8) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 8 < 2 ^ 64 by norm_num)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; omega
  have hWE : crWalk L (cap[p / 256]'hpc) p 8 (entryK crHc crNH (toWord 8) s2.M) := by
    unfold crWalk at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord 8) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord 8) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoop hbX hbX2 hpL hD hX (by omega) 8
    ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ (by norm_num) hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord 8) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord 8) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord 8) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc 8
      ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord 8) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc 8 ⟨entryK crHc crNH (toWord 8) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_sem hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := cr_copy_sem I s4 hM4 hql ha ha2 (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I crCopy s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k1 t ht, crCpRow_of c2,
      xLeafBytes_eq hp hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their row words' cells. -/
theorem cr_posLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ 2 ^ 15 → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + 64 * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < 64,
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M (wB + 64 * q + t) =
          crRowW (xLeafBytes L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + 64 * j ∨ wB + 64 * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (crPos bX pL capW)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : 64 * (j + 1) = 64 * j + 64 := Nat.mul_succ 64 j
    obtain ⟨b1, b2, b3, b4, b5⟩ := cr_pos_sem hbX hbX2 hpL hD hX s hM hXs hcl hcw hcap (p := j)
      (a := wB + 64 * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (crPos bX pL capW) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (crPos bX pL capW) s)).M r =
        rd (semXIR I (crPos bX pL capW) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (crPos bX pL capW) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := cr_posLoop hD hX hcl hcw hcap hwB hwB2 m (j + 1) _ (by omega) hM' hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : 64 * (j + 1 + m) = 64 * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by omega) (.inl (by omega)), dk _ (hy _ (by omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · rw [d2 _ hy1 (by omega), dk _ (hy _ hy1), b2 _ hy1 (by omega)]

/-- **The column reads' semantics on a sorted index**: `readIR bX pL capW wB` stores at
`wB + 64 p + t` row word `t` of the reading at position `p < 2^15` (`crRowW`, zeros for an
erasure) and keeps every heap cell outside `[wB, wB + 2^21)`. -/
theorem readIR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M (wB + 64 * p + t) =
        crRowW (xLeafBytes L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (crTape c π L) (readIR bX pL capW wB) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (readIR bX pL capW wB) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 15))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crWA = toWord (wB + 64 * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 15))]) s).M crNp = toWord (2 ^ 15) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | (rw [Nat.mul_zero, Nat.add_zero])
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s
  rw [readIR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 15))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crCp = toWord (2 ^ 15) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (2 ^ 15)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (2 ^ 15)) (crPos bX pL capW)) s0 =
      iterL (semXIR I (crPos bX pL capW)) crCp (2 ^ 15)
        ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 2 ^ 15 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : 64 * (0 + 2 ^ 15) = 2 ^ 21 := by norm_num
  obtain ⟨d1, d2, d3⟩ := cr_posLoop hbX hbX2 hpL hD hX hcl hcw hcap hwB hwB2 (2 ^ 15) 0
    ⟨entryK crCp crNp (toWord (2 ^ 15)) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by omega) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (2 ^ 15)) s0.M) y = _
  rw [hHE y hy1]

end Read2
end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- **`readIR_sem`** (BLUEPRINT §6.2 step 4). On a domain tape of a SNARK proof whose log starts
at tape word `pL`, take a state `s₂` (memory of at least `bX` words) whose `X[0..|L|)` is the
one `idxIR4 bX pL` left from `s`, with `C_rec`'s cap (128 nodes) on the tape at `capW`. After
`readIR bX pL capW wB`, cell `wB + 64 p + t` holds, as a `K` element, word `t` of the row the
log holds under the cap at position `p` (`readRow`, WP-5's first-preimage reading: `64 − crOcc`
zero words, then the leaf's words; zeros for an erasure), for every `p < 2^15`, `t < 64`; every
heap cell outside `[wB, wB + 2^21)` is kept, in particular the index; `Inv` holds. -/
theorem readIR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) :
    (∀ p < 2 ^ 15, ∀ t < 64,
      rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
        (readRow L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 2 ^ 21 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (bX + a) =
        rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := readIR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; omega)
    (.inr (by omega)), w3⟩
  rw [rdK, w1 p hp t ht', crRowW_readRow L cap p ht']

/-- **The word the decoder consumes** after the read: `readWd L cap p t` at `wB + 64 p + t`. -/
theorem readIR_readWd {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 ≤ bX) {p t : ℕ} (hp : p < 2 ^ 15) (ht' : t < 64) :
    rdK (semXIR (extractorInput c π L).toArray (readIR bX pL capW wB) s₂).M (wB + 64 * p + t) =
      readWd L cap p t :=
  (readIR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ hcl hcw hcap hwB hwB2).1 p hp
    t ht'

end Lvm.X
end

-- ===== from `LvmXRead1Defs` =====

section
namespace Lvm.X
open RecursionFast

/-- **The level-1 word the decoder consumes**: leaf word `t` at position `p`. -/
def readWd1 (L : Log) (cap : List Digest) (p t : ℕ) : BF64 := (readRow1 L cap p).getD t 0

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`. -/
theorem read1IR_nw (bX pL capW wB : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) : ¬ Writes (read1IR bX pL capW wB) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [read1IR, cr1Pos, crLd4, cr1CapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    cr1Copy, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA, crWA, cr8, crMk,
    crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  omega

end Lvm.X
end

-- ===== from `LvmXRead1` =====

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- On a position of the level-1 tree, the leaf bytes are the reading under its cap node. -/
theorem xLeafBytes1_eq {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ 12)
    (hpc : p / 32 < cap.length) :
    xLeafBytes1 L cap p = crRdN 5 L (cap[p / 32]'hpc) p := by
  unfold xLeafBytes1 crRdN
  rw [Nat.mod_eq_of_lt hp, show (2 : ℕ) ^ (12 - 7) = 32 from rfl, List.getElem?_eq_getElem hpc]
  all_goals rfl

theorem readRow1_getD (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 48) :
    (readRow1 L cap p).getD t 0 =
      decLE ((((xLeafBytes1 L cap p).getD []).drop (8 * t)).take 8) := by
  rw [List.getD_eq_getElem _ _ (by rw [readRow1_length]; exact ht)]
  simp [readRow1, xRowOf]

/-- **The stored word as a `K` element is the level-1 row's word.** -/
theorem crLeafW_readRow1 (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 48) :
    wK (crLeafW (xLeafBytes1 L cap p) t) = (readRow1 L cap p).getD t 0 := by
  rw [wK_crLeafW, readRow1_getD L cap p ht]

/-- **The cap node's words**: after `cr1CapPs ; crLd4`, `rQ0 … rQ3` hold `cap[p / 32]`. -/
theorem cr1_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW : ℕ} {cap : List Digest}
    (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 32 < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M rQ3] =
      packBytes (cap[p / 32]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (cr1CapPs capW)) := by simp +decide only [cr1CapPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hA : rd (semXIR I (.blk (cr1CapPs capW)) s).M crTA = toWord (capW + 4 * (p / 32)) := by
    simp only [cr1CapPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, show (5 : Word) = toWord 5 from rfl, shr_toWord (by (clear * - hp; omega)) (by norm_num),
      show (2 : Word) = toWord 2 from rfl, shl_toWord (by norm_num) (by (clear * - hcw he; omega)), add_toWord]
    congr 1
    (clear * -; omega)
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by (clear * - hcw he; omega)) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem cr1_wf_copy : WF cr1Copy := by
  simp +decide only [cr1Copy, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK, crWA, crTA, cr8,
    crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + 47` get
`crCpW I x ql ·`; every other heap cell is kept; `crWA` ends at `a + 48`. -/
theorem cr1_copy_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql a : ℕ}
    (hql : ql < 2 ^ 64) (ha : regs ≤ a) (ha2 : a + 48 + 2 < 2 ^ 64) (hsz : a + 48 ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < 48, rd (semXIR I cr1Copy s).M (a + i) = crCpW I x ql i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 48 ≤ y) → rd (semXIR I cr1Copy s).M y = rd s.M y) ∧
    Inv (semXIR I cr1Copy s).M ∧ rd (semXIR I cr1Copy s).M crWA = toWord (a + 48) ∧
    rd (semXIR I cr1Copy s).M crP = rd s.M crP := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hM
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) s
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)]) s
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crNw = toWord 48 ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crWA = toWord (a + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
        s).M crP = rd s.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ | exact hA | (rw [hX, h1]; all_goals rfl)
  rw [cr1Copy, semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
    s = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord 48) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord 48) s0.M) crCw = toWord 48 :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord 48) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord 48) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw 48 ⟨entryK crCw crNw (toWord 48) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 48 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; (clear * - hy; omega)
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I hql ha ha2 (by norm_num) 48 0
    ⟨entryK crCw crNw (toWord 48) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hsz0; omega)) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  refine ⟨fun i hi => d1 i (by (clear * - hi; omega)) (by omega), fun y hy1 hy2 => ?_, d3,
    by rw [d4, Nat.zero_add], ?_⟩
  · rw [d2 y hy1 (by omega)]
    show rd (entryK crCw crNw (toWord 48) s0.M) y = rd s.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  · rw [d5]
    show rd (entryK crCw crNw (toWord 48) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Pos1
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the leaf words of position `p` at `a … a + 47`; `crP := p + 1`,
`crWA := a + 48`; every other heap cell kept. -/
theorem cr1_pos_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < 2 ^ 12) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + 48 + 2 < 2 ^ 64) (hsz : a + 48 ≤ s.M.size) :
    (∀ t < 48, rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M (a + t) =
      crLeafW (xLeafBytes1 L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + 48 ≤ y) →
      rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M ∧
    rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M crWA = toWord (a + 48) ∧
    rd (semXIR (crTape c π L) (cr1Pos bX pL capW) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 32 < cap.length := by rw [hcl]; (clear * - hp; omega)
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (cr1CapPs capW)) crLd4) := ⟨by simp +decide only [cr1CapPs, WF,
    Prim.dst, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (cr1CapPs capW)) crLd4) := ⟨by simp +decide only [cr1CapPs, Lo,
    Prim.dst, regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_lo_ld4⟩
  have q1 := cr1_capLd_sem I s hM (by rw [hcl]; omega) hcap (by (clear * - hp; omega)) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [cr1CapPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3,
        crP, crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (cr1CapPs capW)) crLd4) s
  rw [cr1Pos, semXIR_seq]
  generalize semXIR I (.seq (.blk (cr1CapPs capW)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord 5)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1).M crNH = toWord 5 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord 5)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalkN 5 L (cap[p / 32]'hpc) p 5 s2.M := by
    refine .inl ⟨o2.1, cap[p / 32]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; (clear * - hy; omega)) (by simp only [crNH, regs] at *; (clear * - hy; omega)),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord 5) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord 5) s2.M) crHc = toWord 5 :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord 5) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord 5) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 5 < 2 ^ 64 by norm_num)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; (clear * - hy; omega)
  have hWE : crWalkN 5 L (cap[p / 32]'hpc) p 5 (entryK crHc crNH (toWord 5) s2.M) := by
    unfold crWalkN at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord 5) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord 5) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoopN hbX hbX2 hpL hD hX (by (clear * - hp; omega)) 5
    ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ (by norm_num) hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord 5) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord 5) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord 5) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc 5
      ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord 5) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc 5 ⟨entryK crHc crNH (toWord 5) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_semN hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := cr1_copy_sem I s4 hM4 hql ha ha2 (by (clear * - hsz hsz1 hsz2 hsz3 hsz4; omega)) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I cr1Copy s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; (clear * - ha ha2 ht; omega)), k1 t ht, c2, xLeafBytes1_eq hp hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; (clear * - hy1; omega)), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; (clear * - hs5; omega)), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their leaf words' cells. -/
theorem cr1_posLoop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ 2 ^ 12 → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + 48 * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < 48,
        rd (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M (wB + 48 * q + t) =
          crLeafW (xLeafBytes1 L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + 48 * j ∨ wB + 48 * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (cr1Pos bX pL capW)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by (clear * - h1 h2; omega), fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : 48 * (j + 1) = 48 * j + 48 := Nat.mul_succ 48 j
    obtain ⟨b1, b2, b3, b4, b5⟩ := cr1_pos_sem hbX hbX2 hpL hD hX s hM hXs hcl hcw hcap (p := j)
      (a := wB + 48 * j) (by (clear * - hjm; omega)) hP hA (by (clear * - hwB; omega)) (by (clear * - hbX2 hwB2 hjm; omega)) (by (clear * - hwB2 hjm hsz; omega))
    have hM' : Inv (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M r =
        rd (semXIR I (cr1Pos bX pL capW) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; (clear * - hy; omega)
    have hsz' : bX ≤ (decS crCp (semXIR I (cr1Pos bX pL capW) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := cr1_posLoop hD hX hcl hcw hcap hwB hwB2 m (j + 1) _ (by (clear * - hjm; omega)) hM'
      hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega))),
          b2 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)) (.inr (by (clear * - hwB2 hjm; omega))), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : 48 * (j + 1 + m) = 48 * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by (clear * -; omega)]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by (clear * - hwB ht; omega)) (.inl (by (clear * - ht; omega))), dk _ (hy _ (by (clear * - hwB ht; omega))), b1 t ht]
      · exact d1 q (by (clear * - h1 hq; omega)) (by (clear * - h2; omega)) t ht
    · rw [d2 _ hy1 (by (clear * - hy2; omega)), dk _ (hy _ hy1), b2 _ hy1 (by (clear * - hjm hy2; omega))]

/-- **The level-1 column reads on a sorted index**: `read1IR bX pL capW wB` stores at
`wB + 48 p + t` leaf word `t` of the reading at position `p < 2^12` and keeps every heap cell
outside `[wB, wB + 48 · 2^12)`. -/
theorem read1IR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < 2 ^ 12, ∀ t < 48,
      rd (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M (wB + 48 * p + t) =
        crLeafW (xLeafBytes1 L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 48 * 2 ^ 12 ≤ y) →
      rd (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (read1IR bX pL capW wB) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 12))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crWA = toWord (wB + 48 * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (2 ^ 12))]) s).M crNp = toWord (2 ^ 12) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s
  rw [read1IR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (2 ^ 12))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp →
      rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crCp = toWord (2 ^ 12) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (2 ^ 12)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (2 ^ 12)) (cr1Pos bX pL capW)) s0 =
      iterL (semXIR I (cr1Pos bX pL capW)) crCp (2 ^ 12)
        ⟨entryK crCp crNp (toWord (2 ^ 12)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show 2 ^ 12 < 2 ^ 64 by norm_num)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; (clear * - hy; omega)
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : 48 * (0 + 2 ^ 12) = 48 * 2 ^ 12 := by norm_num
  obtain ⟨d1, d2, d3⟩ := cr1_posLoop hbX hbX2 hpL hD hX hcl hcw hcap hwB hwB2 (2 ^ 12) 0
    ⟨entryK crCp crNp (toWord (2 ^ 12)) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hsz0; omega))
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by (clear * - hq; omega)) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (2 ^ 12)) s0.M) y = _
  rw [hHE y hy1]

end Pos1
end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- **The level-1 column reads** (as v1's `readIR_sem`, tree (12, 48, 7)). -/
theorem read1IR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) :
    (∀ p < 2 ^ 12, ∀ t < 48,
      rdK (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (wB + 48 * p + t) =
        (readRow1 L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + 48 * 2 ^ 12 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M y = rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (bX + a) =
        rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := read1IR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; (clear * - hwB hwB2; omega))
    (.inr (by (clear * - hwB2; omega))), w3⟩
  rw [rdK, w1 p hp t ht', crLeafW_readRow1 L cap p ht']

/-- The same, as the decoder's word (`readWd1`). -/
theorem read1IR_readWd {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {capW wB : ℕ} {cap : List Digest} (hcl : cap.length = 128) (hcw : capW + 512 < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 ≤ bX) {p t : ℕ} (hp : p < 2 ^ 12) (ht' : t < 48) :
    rdK (semXIR (extractorInput c π L).toArray (read1IR bX pL capW wB) s₂).M (wB + 48 * p + t) =
      readWd1 L cap p t :=
  (read1IR_sem hbX hbX2 hpL c π L hs hq ht s hM hsz s₂ hM₂ hsz₂ hX₂ hcl hcw hcap hwB hwB2).1 p hp
    t ht'

end Lvm.X
end

-- ===== from `LvmMPXNodeSem` =====

section
section
namespace Lvm.X
open RecursionFast Lvm

theorem msgsM_ok : ((fsMsgs pX).take (nChainM pX - 1)).all msgOkL = true :=
  layoutM_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem nChainM_le : nChainM pX - 1 ≤ (fsMsgs pX).length := by
  rw [nChainM_eq, layoutM_P20.2.2.2.2.2.2.2.2.2.1]; decide

theorem msgLM_ok {p : ℕ} (hp0 : 0 < p) (hp : p < nChainM pX) :
    (msgL p).1 % 8 = 0 ∧ (msgL p).2 % 8 = 0 ∧ (msgL p).1 + (msgL p).2 ≤ piSize pX ∧
      32 + (msgL p).2 ≤ queryCap := by
  have hl := nChainM_le
  have hm : (fsMsgs pX)[p - 1]'(by omega) ∈ (fsMsgs pX).take (nChainM pX - 1) :=
    List.mem_iff_getElem.mpr ⟨p - 1, by simp; omega, by simp⟩
  have h := List.all_eq_true.mp msgsM_ok _ hm
  unfold msgL
  rw [List.getD_eq_getElem _ _ (by (clear * - hp0 hp hl; omega))]
  simp only [msgOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem msgLM_last : (msgL (nChainM pX)).1 = 286136 := by
  -- from `layoutM_P20`'s `resOffM` (no second kernel evaluation of `fsMsgs pX`)
  have h : resOffM pX = 286184 := layoutM_P20.2.2.2.2.2.2.2.2.1
  rw [resOffM, eBytes] at h
  rw [msgL]
  omega

theorem chTabM_getD {p k : ℕ} (hp : p ≤ nChainM pX) (hk : k < 4) :
    chTabM.getD (4 * p + k) 0 = (tabEntL p).getD k 0 :=
  getD_flatMap4 tabEntL tabEntL_length _ p k (by (clear * - hp; omega)) hk

/-- **The table realises `V_S`'s chain** through `C_main`'s folds. -/
theorem tabW_chTabM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) :
    TabW (extractorInput c π L).toArray (fsQL π) (nChainM pX) chTabM := by
  have hp1 : π.size = 332336 := hs.trans piSize_eq
  refine ⟨chTabM_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTabM_getD hpN (by norm_num), tabEntL, if_neg (by (clear * - hp0; omega))]
    show (toWord (5 + (msgL p).1 / 8)).toNat < 2 ^ 62
    have : (msgL p).1 ≤ 332336 := by
      rcases Nat.lt_or_ge p (nChainM pX) with h | h
      · have := (msgLM_ok hp0 h).2.2.1; rw [piSize_eq] at this; (clear * - this; omega)
      · have hpe : p = nChainM pX := by (clear * - hpN h; omega)
        rw [hpe, msgLM_last]; (clear * -; omega)
    generalize msgL p = m at this
    rw [toNat_toWord (by (clear * - this; omega))]; (clear * - this; omega)
  · obtain ⟨ho, hl, hol, hq⟩ := msgLM_ok hp0 hpN'
    have e0 := chTabM_getD hpN (k := 0) (by norm_num)
    have e1 := chTabM_getD hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntL, if_neg (by (clear * - hp0; omega))]
    have hz : (fsQL π p st).size = 32 + (msgL p).2 := by
      rw [fsQL, if_neg (by (clear * - hp0; omega)), ByteArray.size_append, extract_size π (by (clear * - hs hp1 ho hl hol; omega)), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; (clear * - hs hp1 ho hl hol; omega), fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQL_data p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgL p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · rw [piSize_eq] at hol
      generalize msgL p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by (clear * - ho; omega)⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by (clear * - hl; omega)⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by (clear * - h4 hj hol; omega)), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by (clear * -; omega),
        tape_getD_proof c π L (by rw [hp1]; (clear * - h4 hj hol; omega)), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hp1]; omega) (by (clear * - h4 hj; omega))]

/-- **`chainLM_spec`**: the machine's chain answers are the first-match chain's. -/
theorem chainLM_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChainM pX, ∀ a, fmAns (fsQL π) zeroDL L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray chainLM s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray chainLM s).M y = rd s.M y) := by
  have hT : ∀ p st, 0 < p → stateIn (fsQL π p st) = some st := fun p st hp => stateIn_fsQL π hp st
  obtain ⟨-, hans, hheap⟩ := chainIR_sem c π L (hs_posL hs) hq ht (N := nChainM pX)
    (by rw [nChainM_eq]; norm_num) (tabW_chTabM c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQL, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChainM pX) (st₀ := zeroDL) hT hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChainM pX) (st₀ := zeroDL) (L := L) (T := fsQL π) hT hS).1
  have hpl : p < (scanC (fsQL π) (nChainM pX) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQL π) (nChainM pX) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [show chainLM = chainIR (posL (piSize pX)) (nChainM pX) chTabM sdL from rfl, hans p hpl m hm, hg]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **A level-0 layout exists** below `2^26` (non-vacuity): workspace at `2^23`, word at `2^24`, `α` at `2^20`, `f`
at `2^20 + 64`. -/
theorem decMP0Lay_example (sz : ℕ) (hsz : 2 ^ 26 ≤ sz) :
    DecM0Lay 19 19 17 40 8 (2 ^ 23) (2 ^ 24) (2 ^ 20) (2 ^ 20 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, wsM]) <;> norm_num <;> omega

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem crG_wf_copy (z occ : ℕ) : WF (crCopyG z occ) := by
  simp +decide only [crCopyG, crZeroG, crZeroBody, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK,
    crWA, crTA, cr8, crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **`C_main`'s level-`i` cap from π**: `capNM i` digests at π word `capOffM pX i / 8`. -/
def capM (π : Proof) (i : ℕ) : List Digest :=
  (List.range (capNM i)).map fun e => hdD π (capOffM pX i / 8 + 4 * e)

/-- **The residual's coefficient `v`** from π (`E` scalars of 3 words at π word `resOffM / 8`). -/
def resEM (π : Proof) (v : ℕ) : BF64.Ext3 :=
  mkE (wK (pw π (resOffM pX / 8 + 3 * v))) (wK (pw π (resOffM pX / 8 + 3 * v + 1)))
    (wK (pw π (resOffM pX / 8 + 3 * v + 2)))

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem den_SM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memM + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memM mpwX (extIRWith (piSize pX) decXM) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray decXM s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0' : Inv (initSt (memM + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWith (pz := piSize pX) wf_decXM).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parse_o, initSt_o], ?_⟩
  have hk : rd (semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parse_isK _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : rd (semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 := by
    rw [parse_regs _ I _ h0', hI, getD_toArray, tape_getD4, hs]
    rw [if_pos (by rfl)]; decide
  rw [den, extIRWith, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

/-- **`EXM` on an `S` proof with `b = 0`**, on every log: the leaf witness of its header. -/
theorem EXM_leaf (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EXM A c π L = some (leafW π) := by
  by_cases hD : InDomE c π L
  · rw [EXM, if_pos hD, EdXM, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_SM c π L hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decXM, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EXM, if_neg hD, EoutX, if_pos h0, if_pos hs, if_pos hb]

/-- **`EXM` on an `S` node proof outside the domain**: the search under the key the proof carries. -/
theorem EXM_node_out (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EXM A c π L = search A (hdD π 2) c := by
  rw [EXM, if_neg hD, EoutX, if_pos h0, if_pos hs, if_neg hb]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The stream block**: from the decoded window at `winM`, the statement's stream words at `mBM`. -/
theorem streamM_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s : St) (hM : Inv s.M)
    (hsz : memM ≤ s.M.size) (out : List BF64)
    (hW : ∀ j < 2 ^ 20, rd s.M (winM + j) = BF64.toBitVec (out.getD j 0)) :
    (∀ i < 2 ^ 19, rd (semXIR (extractorInput c π L).toArray streamM s).M (mBM + i) = wStreamM π out i) ∧
    (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray streamM s).M y = rd s.M y) ∧
    Inv (semXIR (extractorInput c π L).toArray streamM s).M ∧
    (semXIR (extractorInput c π L).toArray streamM s).M.size = s.M.size ∧
    (semXIR (extractorInput c π L).toArray streamM s).o = s.o := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0
  have hwin := winM_eq
  simp only [memM] at hsz
  suffices H : (∀ i < 2 ^ 19, rd (semXIR I streamM s).M (mBM + i) = wStreamM π out i) ∧
      (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) → rd (semXIR I streamM s).M y = rd s.M y) ∧
      Inv (semXIR I streamM s).M from ⟨H.1, H.2.1, H.2.2, size_sem I _ s, sem_o I _ s rfl⟩
  obtain ⟨b1, b2, hM1, z1, -⟩ := readAt_val I s hM (d := eW) (pos := 19) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [streamM, semXIR_seq]
  generalize semXIR I (readAt eW 19) s = s1 at b1 b2 hM1 z1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have w2 : WF (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) := by
    simp +decide [WF, Prim.dst, eA, eW]
  have hM2 := inv_sem I w2 hM1
  have z2 := size_sem I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1
  have r2 : rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M eW =
      if I.getD 19 0 < toWord (2 ^ 18 + 1) then 1 else 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, eW]; (clear * - hsz z1 z2; omega)), rd_set_ne (by decide),
      rd_set_self (by simp only [eA]; (clear * - hsz z1 z2; omega)), b1]
    rfl
  have k2 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M y = rd s.M y :=
    fun y hy => by
      simp only [regs] at hy
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by simp only [eW]; (clear * - hy; omega)), rd_set_ne (by simp only [eA]; (clear * - hy; omega)),
        b2 _ (by simp only [eW]; (clear * - hy; omega)) (by simp only [rA]; (clear * - hy; omega))]
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1 = s2 at hM2 z2 r2 k2
  have hn : I.getD 19 0 = pw π 14 := by rw [show (19 : ℕ) = 5 + 14 from rfl, tape_pw c π L hs (by norm_num)]
  rw [hn] at r2
  have hsz2 : memM ≤ s2.M.size := by rw [z2, z1]; simp only [memM]; omega
  simp only [memM] at hsz2
  rw [semXIR_ite]
  by_cases hsm : pw π 14 < toWord (2 ^ 18 + 1)
  · rw [if_pos hsm] at r2
    rw [if_neg (by rw [r2]; decide)]
    obtain ⟨m1, m2, m3⟩ := mcpIR_sem I s2 hM2 (n := 2 ^ 19) (src := winM) (str := 2) (dst := mBM) (by norm_num)
      (by rw [hwin]; norm_num) (by norm_num) (by simp only [regs, mBM]; norm_num) (by simp only [mBM]; norm_num)
      (by simp only [mBM]; (clear * - hsz z1 z2; omega)) (fun i hi => .inr (by rw [hwin]; simp only [mBM]; (clear * - hi; omega)))
      (fun i hi => by rw [hwin]; simp only [regs]; (clear * - hi; omega))
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; (clear * - hi; omega)), hW _ (by (clear * - hi; omega)), wStreamM, if_pos hsm]
    · rw [m2 y hy h, k2 y hy]
  · rw [if_neg hsm] at r2
    rw [if_pos r2]
    obtain ⟨m1, m2, m3⟩ := mcpIR_sem I s2 hM2 (n := 2 ^ 19) (src := winM + 2 ^ 19) (str := 1) (dst := mBM)
      (by norm_num) (by rw [hwin]; norm_num) (by norm_num) (by simp only [regs, mBM]; norm_num)
      (by simp only [mBM]; norm_num) (by simp only [mBM]; (clear * - hsz z1 z2; omega))
      (fun i hi => .inr (by rw [hwin]; simp only [mBM]; (clear * - hi; omega)))
      (fun i hi => by rw [hwin]; simp only [regs]; (clear * - hi; omega))
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; (clear * - hi; omega)), Nat.one_mul, Nat.add_assoc,
        hW _ (by (clear * - hi; omega)), wStreamM, if_neg hsm]
    · rw [m2 y hy h, k2 y hy]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem capM_length (π : Proof) (i : ℕ) : (capM π i).length = capNM i := by simp [capM]

theorem capOffM_div : capOffM pX 0 / 8 = 748 ∧ capOffM pX 1 / 8 = 17732 ∧ capOffM pX 2 / 8 = 28751 := by
  rw [layoutM_P20.2.2.2.2.2.1, layoutM_P20.2.2.2.2.2.2.1, layoutM_P20.2.2.2.2.2.2.2.1]; decide

theorem capWM_eq (i : ℕ) : capWM i = 5 + capOffM pX i / 8 := rfl

/-- **π's level-`i` cap on the tape** (`i < 3`): the packed words at `capWM i`. -/
theorem capM_tape (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {i : ℕ} (hi : i < 3) :
    ∀ e (he : e < (capM π i).length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capWM i + 4 * e + m) 0 = (packBytes (capM π i)[e].toList).getD m 0 := by
  intro e he m hm
  have he' : e < 256 := by
    rw [capM_length, capNM] at he; split_ifs at he <;> omega
  have hco : capOffM pX i / 8 ≤ 28751 := by
    obtain ⟨h0, h1, h2⟩ := capOffM_div
    interval_cases i <;> (clear * - h0 h1 h2; omega)
  simp only [capM, List.getElem_map, List.getElem_range, hdD, packBytes_digW (length_wsAt _ _ _)]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [wsAt, List.getElem_map, List.getElem_range]
  rw [capWM_eq, show 5 + capOffM pX i / 8 + 4 * e + m = 5 + (capOffM pX i / 8 + 4 * e + m) by (clear * -; omega),
    tape_pw c π L hs (by (clear * - hm he' hco; omega))]

theorem foldPosM_add (i j : ℕ) : foldPosM pX i j = foldPosM pX i 0 + j := by
  unfold foldPosM; omega

theorem foldPosK_0 {j : ℕ} (hj : j < 6) : foldPosK pX j = foldPosM pX 0 0 + j := by
  rw [foldPosK, if_pos hj, foldPosM_add]
theorem foldPosK_1 {j : ℕ} (hj : j < 4) : foldPosK pX (6 + j) = foldPosM pX 1 0 + j := by
  rw [foldPosK, if_neg (by omega), if_pos (by omega), foldPosM_add, Nat.add_sub_cancel_left]
theorem foldPosK_2 {j : ℕ} (hj : j < 4) : foldPosK pX (10 + j) = foldPosM pX 2 0 + j := by
  rw [foldPosK, if_neg (by omega), if_neg (by omega), foldPosM_add, Nat.add_sub_cancel_left]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem hasOut_chainLM : hasOut chainLM = false := by
  simp only [chainLM, chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

set_option maxRecDepth 20000 in
/-- **`EXM` on an `S` node proof in the domain** (BLUEPRINT §6.2, M′): with no state hit, the 14 fold challenges
answered by the first-match chain (`αk k` at `foldPosK pX k`), and the three decoders succeeding on the readings of
`C_main`'s words under π's caps (`wd₀ wd₁ wd₂`), `alphaE` of the answers (`α₀ α₁ α₂`) and π's residual (`f₂`), the node
witness `Xwit π (wStreamM π out)`. The decoders' inputs are given by their values where the programs read them. -/
theorem EXM_node (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0)
    (hS : ¬ StateHit L) (αk : ℕ → Digest)
    (hα : ∀ k < 14, fmAns (fsQL π) zeroDL L (foldPosK pX k) = some (αk k))
    (wd₀ wd₁ wd₂ : ℕ → ℕ → BF64)
    (hw₀ : ∀ q < 2 ^ 19, ∀ t < 64, wd₀ q t = (readRowG 19 8 17 47 L (capM π 0) q).getD t 0)
    (hw₁ : ∀ q < 2 ^ 16, ∀ t < 48, wd₁ q t = (readRowG 16 7 0 48 L (capM π 1) q).getD t 0)
    (hw₂ : ∀ q < 2 ^ 13, ∀ t < 48, wd₂ q t = (readRowG 13 7 0 48 L (capM π 2) q).getD t 0)
    (α₀ α₁ α₂ : ℕ → BF64.Ext3) (ha₀ : ∀ j < 6, α₀ j = alphaE (αk j))
    (ha₁ : ∀ j < 4, α₁ j = alphaE (αk (6 + j))) (ha₂ : ∀ j < 4, α₂ j = alphaE (αk (10 + j)))
    (f₂ : ℕ → BF64.Ext3) (hf₂ : ∀ v < 2 ^ 9, f₂ v = resEM π v)
    (m₂ : ℕ → BF64.Ext3) (hd₂ : decodeMP2 wd₂ α₂ f₂ = some m₂)
    (m₁ : ℕ → BF64.Ext3) (hd₁ : decodeMP1 wd₁ α₁ m₂ = some m₁)
    (out : List BF64) (hd₀ : decodeMP0 wd₀ α₀ m₁ = some out) :
    EXM A c π L = some (Xwit π (wStreamM π out)) := by
  obtain ⟨hπ, hq, ht⟩ := hD
  rw [EXM, if_pos ⟨hπ, hq, ht⟩, EdXM, Eden]
  obtain ⟨s1, hM1, z1, ho1, hden⟩ := den_SM c π L hs h0
  rw [hden]
  set I := (extractorInput c π L).toArray with hI
  have hLt : L.length ≤ (extractorInput c π L).length := by
    have h1 := length_logEntries L
    rw [tape_eq]
    simp only [List.length_append, logWords, List.length_cons]
    (clear * - h1; omega)
  simp only [memM, mpwX] at z1
  -- the flag
  obtain ⟨b1, -, hM2, z2, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [decXM, semXIR_seq]
  generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 z2 bo
  have h6 : I.getD 6 0 ≠ 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num)]; exact hb
  rw [semXIR_ite, if_neg (by rw [b1]; exact h6), nodeM, semXIR_seq]
  -- 1. the index
  have hM3 := inv_sem I (wf_idxIR4 memM pLX) hM2
  have z3 := size_sem I (idxIR4 memM pLX) s2
  have o3 : (semXIR I (idxIR4 memM pLX) s2).o = s2.o := sem_o I _ s2 rfl
  rw [semXIR_seq]
  generalize hs3 : semXIR I (idxIR4 memM pLX) s2 = s3 at hM3 z3 o3
  have hsz3 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s3.M.size := by rw [z3, z2, z1]
  -- 2. the chain
  obtain ⟨ch1, ch2⟩ := chainLM_spec c π L hs hq ht hS s3 hM3 (by rw [chEnd_v]; (clear * - ht z1 z2 z3; omega))
  have hM4 := inv_sem I (P := chainLM) (wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))) hM3
  have z4 := size_sem I chainLM s3
  have o4 : (semXIR I chainLM s3).o = s3.o := sem_o I _ s3 hasOut_chainLM
  rw [semXIR_seq]
  generalize semXIR I chainLM s3 = s4 at ch1 ch2 hM4 z4 o4
  have hsz4 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s4.M.size := by rw [z4]; exact hsz3
  have hX4 : ∀ a < L.length, rd s4.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [hs3, ch2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))))]
  have hpL : pLX ≤ 2 ^ 60 := by rw [layoutX.1]; norm_num
  have hs2' : memM + L.length + L.length ≤ s2.M.size := by rw [z2, z1, memM_v]; (clear * - hLt; omega)
  -- 3. level 0's word
  rw [show read0M memM pLX (capWM 0) wB0M = readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47 from rfl]
  obtain ⟨r1, r2, r3, hM5⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s4 hM4 (by rw [memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX4 (ht' := 19) (lv := 8) (z := 17) (occ := 47)
    (capW := capWM 0) (wB := wB0M) (cap := capM π 0)
    (fun q hq => by rw [capM_length, capNM, if_pos rfl]; (clear * - hq; omega)) (by rw [capM_length, capWM0_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z5 := size_sem I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4
  have o5 : (semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4).o = s4.o := sem_o I _ s4 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4 = s5 at r1 r2 r3 hM5 z5 o5
  have hX5 : ∀ a < L.length, rd s5.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [r3 a ha, hX4 a ha]
  -- 4. level 1's word
  rw [show read1M memM pLX (capWM 1) wB1M = readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48 from rfl]
  obtain ⟨q1, q2, q3, hM6⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s5 hM5 (by rw [z5, memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX5 (ht' := 16) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 1) (wB := wB1M) (cap := capM π 1)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; (clear * - hq; omega))
    (by rw [capM_length, capWM1_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z6 := size_sem I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5
  have o6 : (semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5).o = s5.o := sem_o I _ s5 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5 = s6 at q1 q2 q3 hM6 z6 o6
  have hX6 : ∀ a < L.length, rd s6.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [q3 a ha, hX5 a ha]
  -- 5. level 2's word
  rw [show read2M memM pLX (capWM 2) wB2M = readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48 from rfl]
  obtain ⟨p1, p2, -, hM7⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s6 hM6 (by rw [z6, z5, memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX6 (ht' := 13) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 2) (wB := wB2M) (cap := capM π 2)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; (clear * - hq; omega))
    (by rw [capM_length, capWM2_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z7 := size_sem I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6
  have o7 : (semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6).o = s6.o := sem_o I _ s6 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6 = s7 at p1 p2 hM7 z7 o7
  have hsz7 : 2 ^ 26 ≤ s7.M.size := by rw [z7, z6, z5]; (clear * - ht z1 z2 z3 z4; omega)
  -- the chain answers, kept by the reads
  have hans : ∀ k < 14, ∀ m < 4, rd s7.M (ansB + 4 * foldPosK pX k + m) = dw (αk k) m := fun k hk m hm => by
    have hp := foldPosK_lt hk
    rw [nChainM_eq] at hp
    rw [p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))), q2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))), r2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))),
      ch1 _ (foldPosK_lt hk) _ (hα k hk) m hm]
    rfl
  -- 6. the fold challenges
  rw [semXIR_seq, acpM, semXIR_seq, semXIR_seq, semXIR_seq]
  obtain ⟨a01, a02, hM8a, z8a, o8a⟩ := acp3IR_sem I s7 hM7 (by (clear * - z1 z2 z3 z4 z5 z6 z7 hsz7; omega)) (src := ansB + 4 * foldPosM pX 0 0)
    (dst := aB0M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 6 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 0 0) aB0M 6) s7 = s8a at a01 a02 hM8a z8a o8a
  obtain ⟨a11, a12, hM8b, z8b, o8b⟩ := acp3IR_sem I s8a hM8a (by (clear * - ht z1 z2 z3 z4 z5 z6 z7 z8a; omega)) (src := ansB + 4 * foldPosM pX 1 0)
    (dst := aB1M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 4 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 1 0) aB1M 4) s8a = s8b at a11 a12 hM8b z8b o8b
  obtain ⟨a21, a22, hM8, z8, o8⟩ := acp3IR_sem I s8b hM8b (by (clear * - ht z1 z2 z3 z4 z5 z6 z7 z8a z8b; omega)) (src := ansB + 4 * foldPosM pX 2 0)
    (dst := aB2M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 4 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 2 0) aB2M 4) s8b = s8 at a21 a22 hM8 z8 o8
  have hsz8 : 2 ^ 26 ≤ s8.M.size := by rw [z8, z8b, z8a]; exact hsz7
  -- 7. the residual
  obtain ⟨f1, f2, hM9, z9, o9⟩ := thcpIR_sem I s8 hM8 (a := resWM) (dst := fB2M) (n := 3 * 2 ^ 9)
    (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - z1 z2 z3 z4 z5 z6 z7 z8a z8b z8 hsz8; omega)))
  generalize semXIR I (thcpIR resWM fB2M (3 * 2 ^ 9)) s8 = s9 at f1 f2 hM9 z9 o9
  have hsz9 : memM ≤ s9.M.size := by rw [z9, memM_v]; omega
  -- the fold challenges in place
  have hA0 : ∀ i < 6, ∀ m < 3, rd s8.M (aB0M + 3 * i + m) = dw (αk i) m := fun i hi m hm => by
    rw [a22 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a12 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a01 i hi m hm,
      show ansB + 4 * foldPosM pX 0 0 + 4 * i + m = ansB + 4 * foldPosK pX i + m by rw [foldPosK_0 hi]; ring,
      hans i (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  have hA1 : ∀ i < 4, ∀ m < 3, rd s8.M (aB1M + 3 * i + m) = dw (αk (6 + i)) m := fun i hi m hm => by
    rw [a22 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a11 i hi m hm, a02 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
      show ansB + 4 * foldPosM pX 1 0 + 4 * i + m = ansB + 4 * foldPosK pX (6 + i) + m by rw [foldPosK_1 hi]; ring,
      hans (6 + i) (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  have hA2 : ∀ i < 4, ∀ m < 3, rd s8.M (aB2M + 3 * i + m) = dw (αk (10 + i)) m := fun i hi m hm => by
    rw [a21 i hi m hm, a12 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a02 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
      show ansB + 4 * foldPosM pX 2 0 + 4 * i + m = ansB + 4 * foldPosK pX (10 + i) + m by rw [foldPosK_2 hi]; ring,
      hans (10 + i) (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  -- the frame of steps 6, 7 (outside the fold challenges and the residual)
  have K79 : ∀ y, regs ≤ y → (y < aB0M ∨ aB2M + 12 ≤ y) → (y < fB2M ∨ fB2M + 3 * 2 ^ 9 ≤ y) →
      rd s9.M y = rd s7.M y := fun y hy h1 h2 => by
    rw [f2 y hy h2, a22 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega))), a12 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega))), a02 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega)))]
  -- 8. level 2's decoder
  have hW2 : ∀ q < 2 ^ 13, ∀ t < 48, rdK s9.M (wB2M + 48 * q + t) = wd₂ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₂ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ p1 q hq t (by omega)
  have hAl2 : ∀ i < 4, rdE s9.M (aB2M + 3 * i) = α₂ i := fun i hi => by
    rw [ha₂ i hi]
    exact rdE_alpha fun m hm => by rw [f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA2 i hi m hm]
  have hF2 : ∀ v < 2 ^ 9, rdE s9.M (fB2M + 3 * v) = f₂ v := fun v hv => by
    rw [hf₂ v hv, rdE_eq, resEM]
    have hc : ∀ m < 3, rd s9.M (fB2M + 3 * v + m) = pw π (resOffM pX / 8 + 3 * v + m) := fun m hm => by
      have hr : resOffM pX / 8 = 35773 := by rw [layoutM_P20.2.2.2.2.2.2.2.2.1]
      rw [Nat.add_assoc, f1 _ (by (clear * - hv hm; omega)), resWM_v, show 35778 + (3 * v + m) = 5 + (resOffM pX / 8 + 3 * v + m) by
        (clear * - hr; omega), tape_pw c π L hs (by (clear * - hv hm hr; omega))]
    have c0 := hc 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at c0
    rw [c0, hc 1 (by norm_num), hc 2 (by norm_num)]
  obtain ⟨e21, e22, e23, hM10⟩ := decMP2IR_sem I s9 hM9 (lay2M hsz9) wd₂ α₂ f₂ hW2 hAl2 hF2
  have z10 := size_sem I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9
  have o10 : (semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9).o = s9.o := sem_o I _ s9 rfl
  rw [decide_eq_true (dec_ok2 hd₂)] at e21
  have hm₂ := e22 m₂ hd₂
  generalize semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9 = s10 at e21 hm₂ e23 hM10 z10 o10
  -- 9. the flag, level 1's decoder
  obtain ⟨s11, hM11, z11, o11, k11, e11⟩ := flagIte_sem I s10 hM10 (a := ok1M dB2M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e21
    (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) okL1)
  rw [okL2, e11, semXIR_seq]
  have hsz11 : memM ≤ s11.M.size := by rw [z11, z10]; exact hsz9
  have K11 : ∀ y, regs ≤ y → (y < dB2M ∨ dB2M + ws1M 13 9 ≤ y) → (y < fB1M ∨ fB1M + 3 * 2 ^ 13 ≤ y) →
      rd s11.M y = rd s9.M y := fun y hy h1 h2 => by rw [k11 y hy, e23 y hy h1 h2]
  have hW1 : ∀ q < 2 ^ 16, ∀ t < 48, rdK s11.M (wB1M + 48 * q + t) = wd₁ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₁ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ q1 q hq t (by omega)
  have hAl1 : ∀ i < 4, rdE s11.M (aB1M + 3 * i) = α₁ i := fun i hi => by
    rw [ha₁ i hi]
    exact rdE_alpha fun m hm => by
      rw [K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA1 i hi m hm]
  have hF1 : ∀ v < 2 ^ 13, rdE s11.M (fB1M + 3 * v) = m₂ v := fun v hv => by
    rw [← hm₂ v hv]
    exact rdE_congr fun m hm => k11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hv hm; omega)))
  obtain ⟨e11', e12, e13, hM12⟩ := decMP1IR_sem I s11 hM11 (lay1M hsz11) wd₁ α₁ m₂ hW1 hAl1 hF1
  have z12 := size_sem I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11
  have o12 : (semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11).o = s11.o := sem_o I _ s11 rfl
  rw [decide_eq_true (dec_ok1 hd₁)] at e11'
  have hm₁ := e12 m₁ hd₁
  generalize semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11 = s12 at e11' hm₁ e13 hM12 z12 o12
  -- 10. the flag, level 0's decoder
  obtain ⟨s13, hM13, z13, o13, k13, e13'⟩ := flagIte_sem I s12 hM12 (a := ok1M dB1M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e11'
    (.seq (decMP0IRW dB0M wB0M aB0M fB0M) okL0)
  rw [okL1, e13', semXIR_seq]
  have hsz13 : memM ≤ s13.M.size := by rw [z13, z12, z11, z10]; exact hsz9
  have K13 : ∀ y, regs ≤ y → (y < dB1M ∨ dB1M + ws1M 16 13 ≤ y) → (y < fB0M ∨ fB0M + 3 * 2 ^ 17 ≤ y) →
      rd s13.M y = rd s11.M y := fun y hy h1 h2 => by rw [k13 y hy, e13 y hy h1 h2]
  have hW0 : ∀ q < 2 ^ 19, ∀ t < 64, rdK s13.M (wB0M + 64 * q + t) = wd₀ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      q2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₀ q hq t ht']
    exact (show 17 + 47 = 64 from rfl) ▸ r1 q hq t (by omega)
  have hAl0 : ∀ i < 6, rdE s13.M (aB0M + 3 * i) = α₀ i := fun i hi => by
    rw [ha₀ i hi]
    exact rdE_alpha fun m hm => by
      rw [K13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
        f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA0 i hi m hm]
  have hF0 : ∀ v < 2 ^ 17, rdE s13.M (fB0M + 3 * v) = m₁ v := fun v hv => by
    rw [← hm₁ v hv]
    exact rdE_congr fun m hm => k13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hv hm; omega)))
  obtain ⟨e01, e02, e03, hM14⟩ := decMP0IRW_sem I s13 hM13 (lay0M hsz13) wd₀ α₀ m₁ hW0 hAl0 hF0
  have z14 := size_sem I (decMP0IRW dB0M wB0M aB0M fB0M) s13
  have o14 : (semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13).o = s13.o := sem_o I _ s13 rfl
  rw [decide_eq_true (dec_ok0 hd₀)] at e01
  have hout := e02 out hd₀
  generalize semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13 = s14 at e01 hout e03 hM14 z14 o14
  -- 11. the flag, the stream block, the node output
  obtain ⟨s15, hM15, z15, o15, k15, e15⟩ := flagIte_sem I s14 hM14 (a := okM dB0M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e01
    (.seq streamM (outIR mBM))
  rw [okL0, e15, semXIR_seq]
  have hsz15 : memM ≤ s15.M.size := by rw [z15, z14]; exact hsz13
  obtain ⟨st1, -, hM16, z16, o16⟩ := streamM_sem c π L hs s15 hM15 hsz15 out fun j hj => by
    rw [k15 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hj; omega))), ← rdK_toBitVec, hout j (by omega)]
  rw [outIR_sem c π L hs _ hM16 (mB := mBM) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by rw [z16]; ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - z1 z2 z3 z4 z5 z6 z7 z8a z8b z8 z9 z10 z11 z12 z13 z14 z15 hsz15; omega))) (wStreamM π out) st1, o16, o15,
    o14, o13, o12, o11, o10, o9, o8, o8b, o8a, o7, o6, o5, o4, o3, bo, ho1, Array.toList_empty, List.nil_append]
  exact decodeWit_outWords π _

end Lvm.X
end
