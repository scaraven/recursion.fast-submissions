-- lvm2 X-REC2 (helper DEC): the semantics of the level-1 column reads. Adapted from this entry's
-- `LvmXRead.lean`/`LvmXRead2.lean` (v1's `cr_capLd_sem`, `cr_nodeLoop`, `cr_copy_sem`, `cr_pos_sem`,
-- `cr_posLoop`, `readIR_sem4`, `readIR_sem`, `readIR_readWd`) at tree (12, 48, 7).
import LvmXRead1Defs

-- (GOLF2: 11 declarations that `certified` does not use moved verbatim to `LvmMPXNodeSemOff`, outside its import closure.)

/-!
# `read1IR_sem`: the level-1 column reads compute `readRow1`

After the index (`idxIR4`), `read1IR bX pL capW wB` stores `readRow1 L cap p` at `wB + 48p + t`
(`p < 2^12`, `t < 48`); the index and the heap outside `[wB, wB + 48·2^12)` are kept.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The pure reading at level 1 -/

/-- The reading under a cap node `d0` after `n` steps down: the leaf's bytes. -/
def crRdN (n : ℕ) (L : Log) (d0 : Digest) (p : ℕ) : Option (List UInt8) :=
  (xDescend L n d0 p).bind fun d => (xFindA L d).map fun e => xQb e.1

/-! ## The cap node at level 1 -/

/-! ## The walk of `n` steps -/

/-- **The walk's state at height `h`** for a walk of `n` steps from the cap node `d₀` (v1's
`crWalk` at `n = 8`). -/
def crWalkN (n : ℕ) (L : Log) (d0 : Digest) (p h : ℕ) (M : Mem) : Prop :=
  (rd M crOk = 1 ∧ ∃ d : Digest, [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = packBytes d.toList ∧
    xDescend L n d0 p = xDescend L h d p) ∨
  (rd M crOk = 0 ∧ xDescend L n d0 p = none)

section Read1

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One node step keeps the walk's state**, one level down. -/
theorem cr_nodeWalkN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {n : ℕ} {d0 : Digest}
    {p h : ℕ} (hp : p < 2 ^ 62) (hh : h + 1 < 64) (hP : rd s.M crP = toWord p)
    (hH : rd s.M crHc = toWord (h + 1)) (hW : crWalkN n L d0 p (h + 1) s.M) :
    crWalkN n L d0 p h (semXIR (crTape c π L) (crNode bX pL) s).M := by
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
theorem cr_nodeLoopN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {n : ℕ} {d0 : Digest} {p : ℕ} (hp : p < 2 ^ 62) :
    ∀ (m : ℕ) (s : St), m < 64 → Inv s.M → (∀ a < L.length, rd s.M (bX + a) = Xi a) →
      rd s.M crP = toWord p → rd s.M crHc = toWord m → crWalkN n L d0 p m s.M →
      crWalkN n L d0 p 0 (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      Inv (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M ∧
      (∀ x, regs ≤ x → rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M x = rd s.M x) ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crP = rd s.M crP ∧
      rd (iterL (semXIR (crTape c π L) (crNode bX pL)) crHc m s).M crWA = rd s.M crWA
  | 0, s, _, hM, _, _, _, hW => ⟨hW, hM, fun _ _ => rfl, rfl, rfl⟩
  | m + 1, s, hm, hM, hXs, hP, hH, hW => by
    set I := crTape c π L
    have h1 := cr_nodeWalkN hbX hbX2 hpL hD hX s hM hXs (h := m) hp (by omega) hP hH hW
    have hM1 := inv_sem I (cr_wf_node (bX := bX) (pL := pL)) hM
    have hH1 := hframeK I (crNode bX pL) s cr_loK_node
    have fr : ∀ r, (r = crP ∨ r = crWA ∨ r = crHc) →
        rd (semXIR I (crNode bX pL) s).M r = rd s.M r :=
      fun r hr => frame I _ s (cr_wf_node (bX := bX) (pL := pL)) hM r
        (by rcases hr with rfl | rfl | rfl <;> decide) (cr_node_nw hr)
    have hM' : Inv (decS crHc (semXIR I (crNode bX pL) s)).M := inv_decS hM1 (by decide)
    have hHc : rd (decS crHc (semXIR I (crNode bX pL) s)).M crHc = toWord m :=
      rd_decS_self hM1 (by decide) (by rw [fr _ (.inr (.inr rfl)), hH]) (by (clear * - hm; omega))
    have dk : ∀ r, r ≠ crHc → rd (decS crHc (semXIR I (crNode bX pL) s)).M r =
        rd (semXIR I (crNode bX pL) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hW' : crWalkN n L d0 p m (decS crHc (semXIR I (crNode bX pL) s)).M := by
      unfold crWalkN at h1 ⊢
      rw [dk crOk (by decide), dk rQ0 (by decide), dk rQ1 (by decide), dk rQ2 (by decide),
        dk rQ3 (by decide)]
      exact h1
    have hHp : ∀ x, regs ≤ x → rd (decS crHc (semXIR I (crNode bX pL) s)).M x = rd s.M x :=
      fun x hx => (dk x (by simp only [crHc, regs] at *; (clear * - hx; omega))).trans (hH1 x hx)
    obtain ⟨a1, a2, a3, a4, a5⟩ := cr_nodeLoopN hD hX hp m _ (by (clear * - hm; omega)) hM'
      (fun a ha => by rw [hHp _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a ha])
      (by rw [dk _ (by decide), fr _ (.inl rfl), hP]) hHc hW'
    simp only [iterL]
    refine ⟨a1, a2, fun x hx => (a3 x hx).trans (hHp x hx), ?_, ?_⟩
    · rw [a4, dk _ (by decide), fr _ (.inl rfl)]
    · rw [a5, dk _ (by decide), fr _ (.inr (.inl rfl))]

/-- **The leaf**: after `crLeaf`, `crX` and `crQe` are such that the copy stores the leaf words of
the reading under the cap node `d₀` after `n` steps (`crRdN`). -/
theorem cr_leaf_semN (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {n : ℕ} {d0 : Digest}
    {p : ℕ} (hW : crWalkN n L d0 p 0 s.M) :
    ∃ ql < 2 ^ 64, rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crQe = toWord ql ∧
      ∀ t, crCpW (crTape c π L) (rd (semXIR (crTape c π L) (crLeaf bX pL) s).M crX) ql t =
        crLeafW (crRdN n L d0 p) t := by
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
  have hW0 : crWalkN n L d0 p 0 (semXIR I (.blk [.const crQe 0]) s).M := by
    unfold crWalkN at hW ⊢
    rw [fr0 crOk (by decide), fr0 rQ0 (by decide), fr0 rQ1 (by decide), fr0 rQ2 (by decide),
      fr0 rQ3 (by decide)]
    exact hW
  generalize semXIR I (.blk [.const crQe 0]) s = s0 at hM0 hQ0 hXs0 hW0
  have hs0 := hM0.1
  simp only [regs] at hs0
  rw [semXIR_ite]
  rcases hW0 with ⟨hOk, d, hT, hc⟩ | ⟨hOk, hc⟩
  · rw [hOk, if_neg (by decide), semXIR_seq]
    have hrd : crRdN n L d0 p = (xFindA L d).map fun e => xQb e.1 := by
      rw [crRdN, hc]; rfl
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
    have hrd : crRdN n L d0 p = none := by rw [crRdN, hc]; rfl
    rw [hrd]
    refine ⟨0, by norm_num, by
      show rd (runPrims [] s0.M) crQe = _
      rw [runPrims_nil, hQ0], fun t => ?_⟩
    rw [crCpW_zero, crLeafW_none]

end Read1

/-! ## The copy of 48 words -/

/-! ## One position, the position loop -/

section Pos1

variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

end Pos1

end Lvm.X
