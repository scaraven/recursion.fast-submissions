-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 16; stage S-H2, track L-ext).
import FRXSeed

/-!
# The node branch with the Fiat–Shamir replay

`decN := chainIR nRep chTab seedIR ; logIR ; read0`: the chain replay (the fold challenges at
`ansB + 4p`, `chain_spec`), then the log index and the ladder read of level 0 (`read_spec`). The
chain's memory `[chB, chEnd)` is below the column store (`colBase = 2^25`) and the index (above
`memX = 2^26`).

* `safe_chainIR`: the chain's loop bounds on every SNARK tape (the count is `cnt_sem`'s word
  count, `≤ t`).
* **`decOk_decLN2`**: the branch `kindIR ; ite rKN decN leafIR` meets `DecOk`.
* **`chain_dec`**: `chain_spec` for `seedIR`: the replayed answers are the first-match chain from
  the seed `"FRSEED0" ‖ vkOf π ‖ c ‖ hdr`.
-/

namespace FR.X

open RecursionFast FR.Snd

/-! ## The chain's loop bounds -/

theorem safe_cntIR {I : Array Word} {t : ℕ} (h : (I.getD posL 0).toNat ≤ t / 5) :
    Safe I t cntIR := by
  unfold cntIR
  refine .seq (.loopT (safe_of_noLoopT (by simp [readAt, NoLoopT])) (fun s hM => ?_)
    (safe_of_noLoopT (by simp [cntBody, NoLoopT]))) (.blk _)
  rw [rd_seq_readAt I _ s (by simp [WF, Prim.dst, rP]) hM (by simp [rN, regs])
    (by simp only [posL]; omega)]
  simpa [Aff.eval] using h

theorem wordsOf_le (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    posL + 1 + wordsOf L ≤ (extractorInput c π L).length := by
  have := tape_entries_end c π L hs
  rw [entryOff_length] at this
  simpa only [wordsOf] using this

theorem noLoopT_wordIR (N : ℕ) : NoLoopT (wordIR N) := by
  simp [wordIR, lenIR, qryIR, ansIR, lastIR, recIR, recPre, st4IR, nextIR, nextPre, stAt, stNext,
    NoLoopT]

/-- **The chain's loop bounds** on every SNARK tape: the walk's count is `|L| ≤ t/5`, the scan's
is the log's word count `≤ t`. -/
theorem safe_chainIR (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (N : ℕ)
    (tab : List Word) {sd : XIR} (hsd : NoLoopT sd) (hwf : WF sd) (hw : ¬ Writes sd rCn5) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (chainIR N tab sd) := by
  set I := (extractorInput c π L).toArray
  have hc : Safe I (extractorInput c π L).length cntIR := safe_cntIR (tape_count_le c π L hs ht)
  refine .loopT (.seq hc (.seq (safe_of_noLoopT (noLoopT_storesIR _ _)) (.seq (safe_of_noLoopT hsd)
    (.blk _)))) (fun s hM => ?_) (safe_of_noLoopT (noLoopT_wordIR N))
  rw [semXIR_seq, semXIR_seq, semXIR_seq]
  have hM1 := inv_sem I wf_cntIR hM
  have c1 := cnt_sem c π L hs hq ht s hM
  generalize semXIR I cntIR s = s1 at hM1 c1
  have hM2 := inv_sem I (wf_storesIR chB tab) hM1
  have c2 := frame I (storesIR chB tab) s1 (wf_storesIR _ _) hM1 rCn5 (by decide)
    (lo_free_storesIR _ _ _ (by decide) (by decide) (by decide))
  generalize semXIR I (storesIR chB tab) s1 = s2 at hM2 c2
  have c3 := frame I sd s2 hwf hM2 rCn5 (by decide) hw
  have hM3 := inv_sem I hwf hM2
  generalize semXIR I sd s2 = s3 at hM3 c3
  have c4 := frame I (.blk startPs) s3 (by simp [WF, startPs, Prim.dst, rWp, rEo, rPi, rTl, rTh,
    rTo, rMt]) hM3 rCn5 (by decide) (by simp [Writes, startPs, Prim.dst, rCn5, rWp, rEo, rPi, rTl,
    rTh, rTo, rMt])
  have hw := wordsOf_le c π L hs
  simp only [posL] at hw
  rw [c4, c3, c2, c1, toNat_toWord (by omega)]
  simp only [Aff.eval, Nat.zero_add, Nat.one_mul, Nat.div_one]
  omega

/-! ## The node branch -/

/-- **The node branch**: the chain replay, then the log index and the read of level 0. -/
def decN : XIR := .seq (chainIR nRep chTab seedIR) decRead

/-- **The SNARK branch**: a node runs `decN`, a leaf outputs its witness. -/
def decLN2 : XIR := .seq kindIR (.ite rKN decN leafIR)

theorem noWrite_seedIR {i : ℕ} (h1 : i ≠ rSa) (h2 : i ≠ rSb) (h3 : i ≠ rSk) (h4 : i ≠ rSad)
    (h5 : i ≠ rA) (h6 : i ≠ cTmp) : ¬ Writes seedIR i := fun h => by
  rcases writes_sdList _ h with h | h | h | h | h | h <;> contradiction

theorem wf_decN : WF decN :=
  ⟨wf_chainIR nRep chTab (wf_sdList _) (noWrite_seedIR (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)), decOk_decRead.wf⟩

theorem cost_decN (t : ℕ) : cost decN t ≤ 18002 * 10 ^ 6 + 2558 * t := by
  have h1 := cost_seedIR t
  have e : cost decN t = 34 + 9 * (4 * (nRep + 1)) + cost seedIR t + t / 5 * 24 + t * 179 +
      (2592 + t / 5 * 11871 + 18001952782 + 1) + 1 := by
    rw [decN, cost, cost_chainIR, chTab_length, decRead, cost, cost_logIR, cost_read0]
  simp only [nRep] at e
  rw [e]
  have : t / 5 * 11895 ≤ 2379 * t := by omega
  omega

theorem sizeIR_decN : sizeIR decN ≤ 21000 := by
  have := size_seedIR
  have e : sizeIR decN = 284 + 10 * (4 * (nRep + 1)) + sizeIR seedIR + (294 + 570 + 1) + 1 := by
    rw [decN, sizeIR, sizeIR_chainIR, chTab_length, decRead, sizeIR, sizeIR_read0,
      sizeIR_logIR_eq]
  simp only [nRep] at e
  omega

theorem decOk_decLN2 : DecOk decLN2 where
  wf := ⟨by simp [kindIR, readAt, WF, Prim.dst, rB, rK2, rKN, rKL, rA], wf_decN,
    by simp [leafIR, outAt, readAt, WF, Prim.dst, rK2, rV2, rA]⟩
  safe := fun c π L hs hq ht => .seq (safe_of_noLoopT noLoopT_leaf.1)
    (.ite (.seq (safe_chainIR c π L hs hq ht nRep chTab (noLoopT_sdList _) (wf_sdList _)
      (noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
      (decOk_decRead.safe c π L hs hq ht)) (safe_of_noLoopT noLoopT_leaf.2))
  cost := fun t => by
    have h := cost_decN t
    have e : cost leafIR t = 32 := by simp [leafIR, outAt, readAt, cost, blkSteps]
    have e2 : cost kindIR t = 15 := by simp [kindIR, readAt, cost, blkSteps]
    have h2 : decBudget t = 211106098315264 + 8176 * t := by
      simp only [decBudget, fuelBase, fuelPerWord]; norm_num
    rw [h2, decLN2, cost, cost, e, e2]
    omega
  outs := fun t => by
    have h1 : outs decRead t = 0 := by simp [decRead, outs, outs_logIR, outs_readIR, read0]
    have h2 : outs decN t = 0 := by
      rw [decN, outs, h1, outs_chainIR nRep t chTab (sd := seedIR) (outs_sdList t _)]
    simp [decLN2, kindIR, leafIR, outAt, readAt, outs, h2, outCap]
  size := by
    have := sizeIR_decN
    have e : sizeIR leafIR = 35 := by simp [leafIR, outAt, readAt, sizeIR, blkSteps]
    have e2 : sizeIR kindIR = 15 := by simp [kindIR, readAt, sizeIR, blkSteps]
    rw [decLN2, sizeIR, sizeIR, e, e2]; omega

/-! ## The chain's answers in the branch -/

/-- **The replayed answers** (`chain_spec` for the seed block): on a domain tape of a SNARK proof
whose log has no state hit, at every position `p < nRep` that the first-match chain from the seed
`"FRSEED0" ‖ vkOf π ‖ c ‖ hdr` answers with `a`, the chain scan leaves `a`'s words at
`ansB + 4p`. -/
theorem chain_dec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (st₀ : Digest) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) {p : ℕ}
    (hp : p < nRep) {a : Digest} (ha : fmAns (fsQ (vkOf π) c π) st₀ L p = some a) {m : ℕ}
    (hm : m < 4) :
    rd (semXIR (extractorInput c π L).toArray (chainIR nRep chTab seedIR) s).M (ansB + 4 * p + m) =
      (packBytes a.toList).getD m 0 :=
  chain_spec (vkOf π) c π L hs hq ht hS (zeroD := st₀) (seedOK_seedIR c π L hs st₀) s hM hsz hp
    ha hm

end FR.X
