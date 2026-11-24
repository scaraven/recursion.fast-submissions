-- lvm6 X5 (BLUEPRINT v3 §3, §5 T8; X2 §4 item 3): the whole extractor program of lvm6, its specification `EX6`,
-- `computes6` (fuel `2^47 + 8192 t`, memory `2^30 + 3t`) and `ext_eq6` against `ExtSpec6` (the pinned member of
-- the opening's candidates). The frame is season 1's `LvmXComputes` (`extIRWith`, `Safe`, `den_of_run`) and
-- `Lvm6WOnly.eden_W`, with lvm6's memory and fuel.
import Lvm6XNode
import Lvm6XCost
import Lvm6XChain
import Lvm6XBridge
import Lvm6WOnly
import Lvm6Stmt

/-!
# The extractor `extX6`, `computes6`, `ext_eq6`

**The program** (`extIRWith pz6 (dec6 descX)`, season 1's parse: the `W` branch on byte 0 `≠ 'S'`, which is
`isS`; the `S` branch at `|π| = pz6 = piLenOf P17 = 230,424`; PORT17 X1):

1. `frontIR6`: the log index (`idxIR4` at `bX6 = 2^30`), the chain scan `chain6 P17` (1,055 targets), the Merkle
   inversion of the five commitments (`read6IR i` at `capW6 i`, rows from `wB6 i`);
2. `descX`: the descent over FD1 per level (X4's `roundIR` per round, with the loaders and level transitions not yet
   written): **a parameter** with the structural facts `DescOk6` (well formed, no `loopT`, no output, cost
   `≤ descCost6 + 2^43`);
3. `outIR6`: the tree inversion's output, by header word `b`: `leafOutIR 2^17 colB6 2^18` or `nodeOutIR`.

**`computes6`** (`DescOk6 descX →`): `Computes (extX6 descX) (EX6 descX) fuel6`, through `budget6`.
**`ext_eq6`** (`K.ext = ExtSpec6 I`, `SFront6 … →`): `ExtEq6 (EX6 descX) K`. `SFront6` holds the facts not
proved here, as named fields: the accepted length (V1), the header words on the tape (V1/F1, pure bytes), the
goodness of every level's challenges on accepting logs (`goodL`: W1's doom chain, X4's `GoodL`) and the descent's
result under it (`descends`: X2's readers and chain, X4's `descD_correct`/`roundIR_sem`, W1's deployed instance
`hdom`/`E2` basis/`TailIface`, the loaders, the level transitions). Everything else (dispatch, output stage,
stack-to-witness bridge, decoding of the output words) is proved.

**`size_extX6`** (X6a, F-X5 fixed: the left segment is `rep`s over runs and blocks, `leftSegD`, 16,223 statements
instead of 1,525,793): `extX6 descX` is within `progCap = 2^20` statements whenever the descent has at most `2^19`
(the rest is at most 112,285 statements: the chain scan at most 82,203, the node output 26,849; `P17`).
-/

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm.T
open RecursionFast.WitnessSending (decode)
open LeanVM.Protocol.Compile (Ev)

/-! ## Constants -/

/-- The fixed memory `2^30` words. -/ def mem6 : ℕ := 1073741824
/-- The `S` proof size at `P17` (PORT17; was `P18`'s 238,152). -/ def pz6 : ℕ := 230424
/-- The tape word of the log count. -/ def pL6 : ℕ := 28808
/-- The log index's base (above the fixed memory). -/ def bX6 : ℕ := 1073741824

theorem pz6_eq : pz6 = piLenOf P17 := Lvm6.piLen_P17.symm
theorem pL6_eq : pL6 = posL pz6 := rfl

/-- Level `i`'s rows: `occ6 i · 2^ht6 i` words from `wB6 i`. -/
def wB6 : ℕ → ℕ
  | 0 => 134217728
  | 1 => 268435456
  | 2 => 301989888
  | 3 => 318767104
  | _ => 327155712

/-- Level `i`'s cap: tape word `5 + off/8`, `off` its byte offset in `π` (`hdrLen P17 + bytesOf` of the items
before `cap i`: 824, 63,936, 152,608, 184,256, 204,480 at `P17`, all `≡ 0 mod 8`; `frontD`). -/
def capW6 : ℕ → ℕ
  | 0 => 108
  | 1 => 7997
  | 2 => 19081
  | 3 => 23037
  | _ => 25565

/-! ## The program -/

/-- The five Merkle inversions. -/
def readsIR6 : XIR :=
  .seq (read6IR 0 bX6 pL6 (capW6 0) (wB6 0)) (.seq (read6IR 1 bX6 pL6 (capW6 1) (wB6 1))
    (.seq (read6IR 2 bX6 pL6 (capW6 2) (wB6 2)) (.seq (read6IR 3 bX6 pL6 (capW6 3) (wB6 3))
      (read6IR 4 bX6 pL6 (capW6 4) (wB6 4)))))

/-- **Replay**: the log index, the chain scan, the Merkle inversions. -/
def frontIR6 : XIR := .seq (idxIR4 bX6 pL6) (.seq (chain6 P17) readsIR6)

/-- The header word `b`. -/ def rB6 : ℕ := 236

/-- **The output**: by `b` (tape word 6), the leaf witness or the node witness. -/
def outIR6 : XIR := .seq (readAt rB6 6) (.ite rB6 nodeOutIR (leafOutIR nD colB6 stride6))

/-- **The `S` branch** with the descent `descX`. -/
def dec6 (descX : XIR) : XIR := .seq frontIR6 (.seq descX outIR6)

/-- The extractor's IR. -/
def extIR6 (descX : XIR) : XIR := extIRWith pz6 (dec6 descX)

/-- **The extractor program** (`2^30 + 3t` words). -/
def extX6 (descX : XIR) : XProg := toProg mem6 mpwX (extIR6 descX)

/-- **The extractor specification**: the program's denotation on an `S` proof, the witness-sending decoder on a
`W` proof. -/
def EX6 (descX : XIR) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if isS π = true then Eden mem6 mpwX (extIR6 descX) c π L else decode π

/-- **The descent's structural obligations** (X4's `roundIR` per round, the loaders, the copies to `colB6`). -/
structure DescOk6 (descX : XIR) : Prop where
  wf : WF descX
  noLoopT : NoLoopT descX
  outs : ∀ t, outs descX t = 0
  cost : ∀ t, cost descX t ≤ descCost6 + 2 ^ 43

/-! ## Structure -/

theorem wf_readsIR6 : WF readsIR6 :=
  ⟨wf_read6IR .., wf_read6IR .., wf_read6IR .., wf_read6IR .., wf_read6IR ..⟩

theorem noLoopT_readsIR6 : NoLoopT readsIR6 :=
  ⟨noLoopT_read6IR .., noLoopT_read6IR .., noLoopT_read6IR .., noLoopT_read6IR .., noLoopT_read6IR ..⟩

theorem wf_chain6 : WF (chain6 P17) :=
  wf_chainIR _ _ _ wf_sd6 (nw_sd6 _ (by decide) (by decide) (by decide))

theorem wf_frontIR6 : WF frontIR6 := ⟨wf_idxIR4 _ _, wf_chain6, wf_readsIR6⟩

theorem wf_outIR6 : WF outIR6 :=
  ⟨by simp +decide [readAt, WF, Prim.dst, rA, rB6], wf_nodeOutIR, wf_leafOutIR _ _ _⟩

theorem noLoopT_outIR6 : NoLoopT outIR6 :=
  ⟨by simp [readAt, NoLoopT], noLoopT_nodeOutIR, noLoopT_leafOutIR _ _ _⟩

theorem wf_dec6 {descX : XIR} (hD : DescOk6 descX) : WF (dec6 descX) := ⟨wf_frontIR6, hD.wf, wf_outIR6⟩

theorem cost_readsIR6 (t : ℕ) : cost readsIR6 t = 186148454470 + 4 := by
  have h := cost6_reads bX6 pL6 capW6 wB6 t
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldr_append, List.foldr_cons,
    List.foldr_nil] at h
  simp only [readsIR6, cost]
  omega

theorem cost_outIR6 (t : ℕ) : cost outIR6 t = 7957596 := by
  simp only [outIR6, readAt, cost, cost_nodeOutIR, cost_leafOutIR nD colB6 stride6 t (by simp only [nD]; norm_num),
    blkSteps, List.length_cons, List.length_nil]
  simp only [nD]
  norm_num

theorem outs_outIR6 (t : ℕ) : outs outIR6 t ≤ 619166 := by
  have h := outs_nodeOutIR t
  simp only [outIR6, readAt, outs, outs_leafOutIR nD colB6 stride6 t (by simp only [nD]; norm_num)]
  simp only [nD]
  omega

/-- **The `S` branch's cost**: the readers (`cost6_reads`), the descent within `descCost6 + 2^43` (`descCost6_le`), the
rest in `budget6`'s `x ≤ 2^44` and `8000 t`. -/
theorem cost_dec6_le {descX : XIR} (hD : DescOk6 descX) (t : ℕ) :
    cost (dec6 descX) t ≤ 2 ^ 47 - 2 ^ 31 + 8000 * t := by
  have hr := cost_readsIR6 t
  have hd := hD.cost t
  have hc := cost_chain6 P17 t
  have hn := chainOK6_P17.nCh
  have hdl := descCost6_le
  rw [cost_sd6] at hc
  have e : cost (dec6 descX) t = cost (idxIR4 bX6 pL6) t + (cost (chain6 P17) t + cost readsIR6 t + 1) + 1 +
      (cost descX t + cost outIR6 t + 1) + 1 := rfl
  rw [e, cost_idxIR4, hr, cost_outIR6, hc]
  have h47 : (2 : ℕ) ^ 47 - 2 ^ 31 = 140735340871680 := by norm_num
  have h45 : (2 : ℕ) ^ 45 = 35184372088832 := by norm_num
  have h43 : (2 : ℕ) ^ 43 = 8796093022208 := by norm_num
  have h11 : (2 : ℕ) ^ 11 = 2048 := by norm_num
  rw [h47]
  rw [h45] at hdl
  rw [h43] at hd
  rw [h11] at hn
  generalize descCost6 = D at hd hdl
  generalize nCh6 P17 = N at hn ⊢
  generalize cost descX t = cd at hd ⊢
  omega

theorem outs_dec6 {descX : XIR} (hD : DescOk6 descX) (t : ℕ) : outs (dec6 descX) t ≤ outCap := by
  have h1 := outs_outIR6 t
  simp only [dec6, frontIR6, readsIR6, chain6, outs, outs_idxIR4, outs_read6IR, hD.outs,
    outs_chainIR _ _ t _ (show outs sd6 t = 0 by simp [sd6, outs]), outCap]
  omega

/-! ## The program's size -/

theorem sizeIR_idxIR6 : sizeIR (idxIR4 bX6 pL6) = 294 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem sizeIR_chain6_le : sizeIR (chain6 P17) ≤ 82203 := by
  have hn := chainOK6_P17.nCh
  rw [chain6, sizeIR_chainIR, tab6_length]
  have hs : sizeIR sd6 ≤ 11 := by simp only [sd6, sizeIR, blkSteps, List.length_cons, List.length_nil]; norm_num
  generalize nCh6 P17 = N at hn ⊢
  generalize sizeIR sd6 = D at hs ⊢
  omega

/-! The main size proofs below (`size_extX6`, and `sizeIR_F` downstream) rewrite with `rw` and generic equations
only. A `simp only [def]` on a goal that holds a closed `sizeIR` of a large part (`chain6 P18`, `fillIR`) leaves
a definitional step that the kernel's replay checks by evaluating that size (`Nat` addition reduces both arguments
to literals): seconds to a minute of kernel time a proof. -/

/-- `sizeIR` of a sequence (the defining equation, for `rw`). -/
theorem sizeIR_seq (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := rfl

/-- The compiled program's statement count: the prologue's `7`, `P`'s, and the sequence's `1`. -/
theorem body_size_toProg (mem mpw : ℕ) (P : XIR) : (toProg mem mpw P).body.size = 7 + sizeIR P + 1 := by
  simp only [toProg, size_compile, sizeIR, initPs, blkSteps, List.length_cons, List.length_nil]
  rfl

theorem sizeIR_readsIR6 : sizeIR readsIR6 = 2819 := by
  simp only [readsIR6, sizeIR, sizeIR_read6IR]

theorem sizeIR_outIR6 : sizeIR outIR6 = 26904 := by
  simp only [outIR6, readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, sizeIR_nodeOutIR,
    sizeIR_leafOutIR]
  norm_num

/-- **`Open6.size`**: the extractor is within `progCap` statements when the descent has at most `2^19`. -/
theorem size_extX6 {descX : XIR} (h : sizeIR descX ≤ 2 ^ 19) : (extX6 descX).body.size ≤ progCap := by
  have hc := sizeIR_chain6_le
  rw [extX6, body_size_toProg, extIR6, sizeIR_extIRWith, dec6, frontIR6, sizeIR_seq, sizeIR_seq, sizeIR_seq,
    sizeIR_seq, sizeIR_readsIR6, sizeIR_outIR6, sizeIR_idxIR6]
  generalize sizeIR (chain6 P17) = C at hc ⊢
  generalize sizeIR descX = D at h ⊢
  simp only [progCap]
  omega

/-! ## Loop bounds and `Computes` -/

theorem safe_dec6 {descX : XIR} (hD : DescOk6 descX) (c : Digest) (π : Proof) (L : Log) (hs : π.size = pz6)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (dec6 descX) := by
  refine .seq (.seq ?_ (.seq ?_ (safe_of_noLoopT noLoopT_readsIR6)))
    (.seq (safe_of_noLoopT hD.noLoopT) (safe_of_noLoopT noLoopT_outIR6))
  · exact safe_idxIR4 _ _ (by simp only [pL6]; norm_num) (tape_count_le4 c π L (hs_posL hs) ht)
  · exact safe_chainIR c π L (hs_posL (hs.trans pz6_eq)) hq ht _ _ ⟨trivial, trivial⟩ wf_sd6
      (nw_sd6 _ (by decide) (by decide) (by decide))

/-- What the `S` branch may cost under the fuel `2^47 + 8192 t` and the memory `2^30 + 3t`. -/
theorem fuel_covers6 {dec : XIR} (h : ∀ t, cost dec t ≤ 2 ^ 47 - 2 ^ 31 + 8000 * t) (t : ℕ) :
    mem6 + mpwX * t + cost (extIRWith pz6 dec) t + 8 ≤ fuel6 t := by
  have := h t
  rw [cost_extIRWith]
  simp only [mem6, mpwX, fuel6] at *
  (clear * - this; omega)

/-- **The program halts within the fuel with at most `outCap` words** (season 1's `halts_of_tape`). -/
theorem halts6 {descX : XIR} (hD : DescOk6 descX) (c : Digest) (π : Proof) (L : Log)
    (hπ : π.size ≤ 8 * outCap) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∃ o, (extX6 descX).run (extractorInput c π L) (fuel6 (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap := by
  set inp := extractorInput c π L
  have ha : π.size ≤ 8 * outCap := hπ
  rw [outCap] at ha
  have h4 : inp.toArray.getD 4 0 = toWord π.size := by rw [getD_toArray, tape_getD4]
  have hlen : (π.size + 7) / 8 + 6 ≤ inp.length := tape_length c π L
  have hwf := wf_extIRWith (pz := pz6) (wf_dec6 hD)
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (mem6 + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4
  have h1 : Inv (semXIR I (parseIR pz6) s0).M := inv_sem I hwf.1 h0
  have hpi : rd (semXIR I (parseIR pz6) s0).M rIsSz ≠ 0 → π.size = pz6 := by
    intro h
    rw [parse_regs pz6 I s0 h0, h4] at h
    by_contra hne
    refine h (if_neg fun he => hne ?_)
    have := congrArg BitVec.toNat he
    rwa [toNat_toWord (by (clear * - ha; omega)), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show pz6 < 2 ^ 64 by simp only [pz6]; norm_num)] at this
  have hpo : (semXIR I (parseIR pz6) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I (parseIR pz6) s0 = s1 at h1 hpi hpo
  have hB : BoundsOk I inp.length (extIRWith pz6 (dec6 descX)) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR pz6 _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk : rd s1.M rIsK = 0
    · rw [if_pos hk]
      exact boundsOk_of_safe (safe_wIR (by (clear * - ha; omega)) h4 (by (clear * - hlen; omega))) hwf.2.2 _ h1
    · rw [if_neg hk, boundsOk_ite]
      by_cases hz : rd s1.M rIsSz = 0
      · rw [if_pos hz]; trivial
      · rw [if_neg hz, ← hI]
        exact boundsOk_of_safe (safe_dec6 hD c π L (hpi hz) hq ht) (wf_dec6 hD) _ h1
  have hrun := run_toProg (P := extIRWith pz6 (dec6 descX)) (input := inp) (f := fuel6 inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers6 (cost_dec6_le hD) _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  by_cases hk : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith pz6 (dec6 descX)) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk]
    have hw : (ceil8 (I.getD 4 0)).toNat = (π.size + 7) / 8 := by rw [h4, toNat_ceil8 (by (clear * - ha; omega))]
    have := congrArg List.length ((congrArg (fun s' : St => s'.o.toList) e).trans
      (wIR_sem I _ h1 (by (clear * - ha hw; omega))))
    simp only [hpo, hw, Array.toList_empty, List.nil_append, List.length_map, List.length_range] at this
    rw [this, outCap]
    (clear * - ha hw this; omega)
  · by_cases hz : rd s1.M rIsSz = 0
    · have e : semXIR I (extIRWith pz6 (dec6 descX)) s0 = semXIR I (.blk []) s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_pos hz]
      have hl : (semXIR I (extIRWith pz6 (dec6 descX)) s0).o.toList.length = 0 := by
        rw [e]; simp [semXIR, hpo]
      rw [hl]; exact Nat.zero_le _
    · have e : semXIR I (extIRWith pz6 (dec6 descX)) s0 = semXIR I (dec6 descX) s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]
      have := outs_le (I := I) inp.length (dec6 descX) _ (wf_dec6 hD) h1
        (boundsOk_of_safe (hI ▸ safe_dec6 hD c π L (hpi hz) hq ht) (wf_dec6 hD) _ h1)
      rw [hpo, ← e] at this
      have h2 := outs_dec6 hD inp.length
      simp only [Array.size_empty, Nat.zero_add] at this
      rw [Array.length_toList]; exact this.trans h2

/-- **The extractor on a `W` proof** is the witness-sending decoder, on every log (`Lvm6WOnly.eden_W`). -/
theorem eden6_W (descX : XIR) (c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 64) (hW : isS π = false) :
    Eden mem6 mpwX (extIR6 descX) c π L = decode π := by
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  have h4 : (extractorInput c π L).toArray.getD 4 0 = toWord π.size := by
    rw [getD_toArray, tape_getD4]
  have hw : (ceil8 ((extractorInput c π L).toArray.getD 4 0)).toNat = (π.size + 7) / 8 := by
    rw [h4, toNat_ceil8 hπ]
  have hso := initSt_o (mem6 + mpwX * (extractorInput c π L).length)
  rw [Eden, den, extIR6]
  generalize initSt (mem6 + mpwX * (extractorInput c π L).length) = s0 at h0 hso
  have hwp : WF (parseIR pz6) := (wf_extIRWith (pz := pz6) (dec := .blk []) (by simp [WF])).1
  have h1 : Inv (semXIR (extractorInput c π L).toArray (parseIR pz6) s0).M := inv_sem _ hwp h0
  have hk5 := Lvm6.W.parse_isK pz6 (extractorInput c π L).toArray s0 h0
  have hz5 := parse_regs pz6 (extractorInput c π L).toArray s0 h0
  have hpo : (semXIR (extractorInput c π L).toArray (parseIR pz6) s0).o = s0.o := parse_o _ _ _
  rw [extIRWith, semXIR_seq, semXIR_ite]
  generalize semXIR (extractorInput c π L).toArray (parseIR pz6) s0 = s1 at h1 hk5 hz5 hpo
  rw [hso] at hpo
  by_cases hk : rd s1.M rIsK = 0
  · rw [if_pos hk, wIR_sem _ _ h1 (by rw [hw]; (clear * - hπ; omega)), hpo, hw, WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.nil_append, List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.nil_append, List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [if_neg hk, semXIR_ite]
    have he : π.data.toList = [] := by
      rcases h : π.data[0]? with _ | b
      · rw [Array.getElem?_eq_none_iff] at h
        exact List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      · exfalso
        have hK : (extractorInput c π L).toArray.getD 5 0 &&& 0xFF = kindS := by
          by_contra hn; rw [if_neg hn] at hk5; exact hk hk5
        have h2 := congrArg BitVec.toNat hK
        rw [Lvm6.W.lowByte, getD_toArray, Lvm6.W.tape_byte0 c π L h] at h2
        have hb : b = sByte := UInt8.toNat_inj.mp h2
        have hg : π.data.getD 0 0 = b := by rw [Array.getD_eq_getD_getElem?, h]; rfl
        simp [isS, hg, hb] at hW
    have hsz : π.size = 0 := by
      rw [WitnessSending.size_eq_length, he]; rfl
    have hz : rd s1.M rIsSz = 0 := by
      rw [hz5, h4, hsz, if_neg (by simp only [pz6]; decide)]
    rw [if_pos hz]
    simp [semXIR, hpo, WitnessSending.decode, he, packBytes]

/-- **T8 `computes6`**: the extractor halts within `2^47 + 8192 t` with at most `outCap` words on the contract's
domain, and its output denotes `EX6`. -/
theorem computes6 {descX : XIR} (hD : DescOk6 descX) : Stmt.computes6 (extX6 descX) (EX6 descX) := by
  intro c π L h1 h2 h3
  obtain ⟨o, ho, hl⟩ := halts6 hD c π L h1 h2 h3
  have hwf := wf_extIRWith (pz := pz6) (wf_dec6 hD)
  refine ⟨o, ho, hl, ?_⟩
  have hd := den_of_run (by simp only [regs, mem6]; norm_num) hwf ho
  by_cases hS : isS π = true
  · rw [EX6, if_pos hS, Eden, extIR6, ← hd]
  · rw [EX6, if_neg hS, ← eden6_W descX c π L (lt_of_le_of_lt h1 (by simp only [outCap]; norm_num))
      (by simpa using hS), Eden, extIR6, ← hd]

/-- **The `W` branch** (`Open6.wBranch`). -/
theorem wBranch6 (descX : XIR) (c : Digest) (π : Proof) (L : Log) (hW : isS π = false) :
    EX6 descX c π L = decode π := by
  rw [EX6, if_neg (by simp [hW])]

end Lvm6.X
