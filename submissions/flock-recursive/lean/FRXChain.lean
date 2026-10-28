-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 14: the fold challenges; stage S-H2,
-- track L-ext).
import FRXChainDefs

/-!
# The chain scan on the machine: the program

One pass over the log's words (`chainIR N`), with the next target in hand. The target of position
`p` is a query of `tl` bytes whose packed words are `Ex j`: the first `h` from the header buffer
`H` (cells `hB …`), the rest from the tape at `o` (`Ex j = I[o + j − h]`: an absorb's message is a
slice of π). The seed's header is its 15 words (`h = 15`, no message); every later target's header
is its tag word and the 4 words of the previous answer (`h = 5`). The table at `chB` gives, for
each position `p`, the words `tl, o, tag, 0`.

Per word of the log (`wordIR`): at an entry's length word, `rQw := ⌈|q|/8⌉` and the match flag
`rMt := [|q| = tl]`; at query word `j`, `rMt &&= [word = Ex j]`; at answer word `m`, the word goes
to `rS_m`; after answer word 3, if `rMt` and `p < N` (`recIR`): the answer goes to `ansB + 4p` and
to `H[1 … 4]`, `p += 1`, and the next target is loaded from the table.

The loop count is the log's word count, `rP − posL − 1` after a store-free walk (`cntIR`); its cap
is `t`. Everything inside the loop is straight-line or `ite`: the cost is `t` times a constant.
-/

namespace FR.X

open RecursionFast

/-! ## Registers (user registers `190 …`) and memory -/

/-- The word read. -/ def rWd : ℕ := 190
/-- Its tape position. -/ def rWp : ℕ := 191
/-- The offset in the entry (`0`: the length word). -/ def rEo : ℕ := 192
/-- The entry's query words. -/ def rQw : ℕ := 193
/-- The match flag. -/ def rMt : ℕ := 194
/-- The target's length in bytes. -/ def rTl : ℕ := 195
/-- The target's header words. -/ def rTh : ℕ := 196
/-- The target's message on the tape. -/ def rTo : ℕ := 197
/-- The target index `p`. -/ def rPi : ℕ := 198
/-- A flag. -/ def rZ : ℕ := 199
/-- `j` or `m`. -/ def rKj : ℕ := 200
/-- An address. -/ def rAd4 : ℕ := 201
/-- The expected word. -/ def rE : ℕ := 202
/-- Answer word 0. -/ def rS0 : ℕ := 203
/-- Answer word 1. -/ def rS1 : ℕ := 204
/-- Answer word 2. -/ def rS2 : ℕ := 205
/-- Answer word 3. -/ def rS3 : ℕ := 206
/-- The next tag word. -/ def rTg : ℕ := 207
/-- The loop counter. -/ def rCC : ℕ := 208
/-- The loop count. -/ def rCn5 : ℕ := 209
/-- Constant scratch. -/ def rKd : ℕ := 210
/-- Mask scratch. -/ def rMk5 : ℕ := 211

/-- The target table: `4` words per position (`2^23`). -/
def chB : ℕ := 8388608
/-- The header buffer `H` (16 cells; `2^23 + 2^11`). -/
def hB : ℕ := 8390656
/-- The answers: `4` words per position (`2^23 + 2^12`). -/
def ansB : ℕ := 8392704
/-- The end of the chain's region (`ansB + 2^11`). -/
def chEnd : ℕ := 8394752

theorem chB_eq : chB = 8388608 := rfl
theorem hB_eq : hB = 8390656 := rfl
theorem ansB_eq : ansB = 8392704 := rfl
theorem layout_eq : chB = 2 ^ 23 ∧ hB = 2 ^ 23 + 2 ^ 11 ∧ ansB = 2 ^ 23 + 2 ^ 12 := by
  norm_num [chB, hB, ansB]

/-! ## The word step -/

/-- The length word: `rQw := ⌈w/8⌉`, `rMt := [w = tl]`, `eo := 1`. -/
def lenIR : XIR := .blk (ceil8Ps rQw rWd ++ [.op .eq rMt rWd rTl, .const rEo 1])

/-- Query word `j = eo − 1`: the expected word from `H` (`j < h`) or from the tape. -/
def qryIR : XIR :=
  .seq (.blk [.op .sub rKj rEo cOne, .op .ltu rZ rKj rTh])
    (.seq (.ite rZ (.seq (.blk [.const rKd (toWord hB), .op .add rAd4 rKd rKj]) (.load rE rAd4))
        (.seq (.blk [.op .add rAd4 rTo rKj, .op .sub rAd4 rAd4 rTh]) (.input rE rAd4)))
      (.blk [.op .eq rZ rWd rE, .op .and rMt rMt rZ, .op .add rEo rEo cOne]))

/-- `r := w` if `m = k`, else unchanged (branch-free). -/
def setSPs (m r : ℕ) : List Prim :=
  [.const rKd (toWord m), .op .eq rMk5 rKj rKd, .const rKd 0, .op .sub rMk5 rKd rMk5,
   .op .xor rKd r rWd, .op .and rKd rKd rMk5, .op .xor r r rKd]

/-- Answer word `m = eo − qw − 1` into `rS_m`; `rZ := [m = 3]`. -/
def ansPs : List Prim :=
  [.op .sub rKj rEo rQw, .op .sub rKj rKj cOne] ++ setSPs 0 rS0 ++ setSPs 1 rS1 ++ setSPs 2 rS2 ++
    setSPs 3 rS3 ++ [.const rKd 3, .op .eq rZ rKj rKd]

/-- A store of register `r` at `a` (`rAd4 := a` first). -/
def stAt (a r : ℕ) : XIR := .seq (.blk [.const rAd4 (toWord a)]) (.store rAd4 r)

/-- A store of register `r` at `rAd4 + 1`. -/
def stNext (r : ℕ) : XIR := .seq (.blk [.op .add rAd4 rAd4 cOne]) (.store rAd4 r)

/-- Four stores of `rS0 … rS3` at `rAd4, rAd4 + 1, …` (`rAd4` ends at the last). -/
def st4IR : XIR := .seq (.store rAd4 rS0) (.seq (stNext rS1) (.seq (stNext rS2) (stNext rS3)))

/-- `p += 1`, `rAd4 :=` the table entry of `p`. -/
def nextPs : List Prim :=
  [.op .add rPi rPi cOne, .const rKd 4, .op .mul rAd4 rPi rKd, .const rKd (toWord chB),
    .op .add rAd4 rAd4 rKd]

/-- The block of `nextPs`. -/
def nextPre : XIR := .blk nextPs

/-- The next target from the table: `p += 1`, `tl`, `o`, the tag into `H[0]`, `h := 5`. -/
def nextIR : XIR :=
  .seq nextPre
  (.seq (.load rTl rAd4) (.seq (.blk [.op .add rAd4 rAd4 cOne]) (.seq (.load rTo rAd4)
  (.seq (.blk [.op .add rAd4 rAd4 cOne]) (.seq (.load rTg rAd4)
  (.seq (.blk [.const rTh 5]) (stAt hB rTg)))))))

/-- `rAd4 := ansB + 4p`. -/
def recPs : List Prim :=
  [.const rKd 4, .op .mul rAd4 rPi rKd, .const rKd (toWord ansB), .op .add rAd4 rAd4 rKd]

/-- The block of `recPs`. -/
def recPre : XIR := .blk recPs

/-- **The record** of a match at `p`: the answer at `ansB + 4p` and in `H[1 … 4]`, then the next
target (`nextIR`). -/
def recIR : XIR :=
  .seq recPre
    (.seq st4IR (.seq (.blk [.const rAd4 (toWord (hB + 1))]) (.seq st4IR nextIR)))

/-- After answer word 3: record if `rMt` and `p < N`; `eo := 0`. -/
def lastIR (N : ℕ) : XIR :=
  .seq (.blk [.const rKd (toWord N), .op .ltu rZ rPi rKd, .op .and rZ rZ rMt])
    (.seq (.ite rZ recIR (.blk [])) (.blk [.const rEo 0]))

/-- An answer word. -/
def ansIR (N : ℕ) : XIR := .seq (.blk ansPs) (.ite rZ (lastIR N) (.blk [.op .add rEo rEo cOne]))

/-- **One word of the log.** -/
def wordIR (N : ℕ) : XIR :=
  .seq (.input rWd rWp) (.seq (.blk [.const rKd 0, .op .eq rZ rEo rKd])
    (.seq (.ite rZ lenIR (.seq (.blk [.op .ltu rZ rQw rEo]) (.ite rZ (ansIR N) qryIR)))
      (.blk [.op .add rWp rWp cOne])))

/-! ## Before the loop -/

/-- The walk without its store: `rP` ends at the log's end. -/
def cntBody : XIR :=
  .seq (.input rQL rP) (.blk (ceil8Ps rT1 rQL ++ [.op .add rP rP rT1, .const rKc 5,
    .op .add rP rP rKc]))

/-- **The count**: the log's words, `rCn5 := rP − posL − 1` after the walk. -/
def cntIR : XIR :=
  .seq (.seq (.blk [.const rP (toWord (posL + 1))]) (readAt rN posL))
    (.seq (.loopT rCW rN ⟨0, 1, 5⟩ cntBody)
      (.blk [.const rKd (toWord (posL + 1)), .op .sub rCn5 rP rKd]))

/-- Straight-line stores of the words `ws` at `b, b + 1, …`. -/
def storesIR (b : ℕ) : List Word → XIR
  | [] => .blk []
  | w :: ws => .seq (.seq (.blk [.const rAd4 (toWord b), .const rKd w]) (.store rAd4 rKd))
      (storesIR (b + 1) ws)

/-- The registers at the start: the first word, `eo = 0`, `p = 0`, the seed's `tl = 119`,
`h = 15`. -/
def startPs : List Prim :=
  [.const rWp (toWord (posL + 1)), .const rEo 0, .const rPi 0, .const rTl 119, .const rTh 15,
   .const rTo 0, .const rMt 0]

/-- **The chain scan** for `N` targets: the count, the table `tab` at `chB`, the seed's header
(`sd`, which writes `H[0 … 14]`), the start, then the loop over the log's words. -/
def chainIR (N : ℕ) (tab : List Word) (sd : XIR) : XIR :=
  .seq (.seq cntIR (.seq (storesIR chB tab) (.seq sd (.blk startPs))))
    (.loopT rCC rCn5 ⟨0, 1, 1⟩ (wordIR N))

/-! ## Well formed, cost, size -/

theorem wf_storesIR : ∀ (b : ℕ) (ws : List Word), WF (storesIR b ws)
  | _, [] => by simp [storesIR, WF]
  | b, _ :: ws => ⟨by simp [WF, Prim.dst, rAd4, rKd, cTmp], wf_storesIR (b + 1) ws⟩

theorem lo_free_storesIR : ∀ (b : ℕ) (ws : List Word) (i : ℕ), i ≠ rAd4 → i ≠ rKd → i ≠ cTmp →
    ¬ Writes (storesIR b ws) i
  | _, [], i, _, _, _ => by simp [storesIR, Writes]
  | b, _ :: ws, i, h1, h2, h3 => by
    simp only [storesIR, Writes, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
      Prim.dst, exists_eq_left, not_or]
    exact ⟨⟨⟨Ne.symm h1, Ne.symm h2⟩, h3⟩, lo_free_storesIR (b + 1) ws i h1 h2 h3⟩

theorem cost_storesIR (t : ℕ) : ∀ (b : ℕ) (ws : List Word), cost (storesIR b ws) t = 9 * ws.length + 1
  | _, [] => rfl
  | b, _ :: ws => by
    simp only [storesIR, cost, blkSteps, List.length_cons, List.length_nil, cost_storesIR t (b + 1) ws]
    norm_num; ring

theorem size_storesIR : ∀ (b : ℕ) (ws : List Word), sizeIR (storesIR b ws) = 10 * ws.length + 1
  | _, [] => rfl
  | b, _ :: ws => by
    simp only [storesIR, sizeIR, blkSteps, List.length_cons, List.length_nil, size_storesIR (b + 1) ws]
    norm_num; ring

theorem noLoopT_storesIR : ∀ (b : ℕ) (ws : List Word), NoLoopT (storesIR b ws)
  | _, [] => trivial
  | b, _ :: ws => ⟨⟨trivial, trivial⟩, noLoopT_storesIR (b + 1) ws⟩

theorem outs_storesIR (t : ℕ) : ∀ (b : ℕ) (ws : List Word), outs (storesIR b ws) t = 0
  | _, [] => rfl
  | b, _ :: ws => by simp only [storesIR, outs, outs_storesIR t (b + 1) ws]

theorem wf_wordIR (N : ℕ) : WF (wordIR N) := by
  simp [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stAt, stNext, ceil8Ps, WF,
    Prim.dst, rWd, rWp, rEo, rQw, rMt, rTl, rTh, rTo, rPi, rZ, rKj, rAd4, rE, rS0, rS1, rS2, rS3,
    rTg, rKd, rMk5, rKc, rT2, cTmp]

theorem not_writes_wordIR_rCC (N : ℕ) : ¬ Writes (wordIR N) rCC := by
  simp [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stAt, stNext, ceil8Ps, Writes,
    Prim.dst, rWd, rWp, rEo, rQw, rMt, rTl, rTh, rTo, rPi, rZ, rKj, rAd4, rE, rS0, rS1, rS2, rS3,
    rTg, rKd, rMk5, rKc, rT2, cTmp, rCC]

theorem wf_cntIR : WF cntIR := by
  simp [cntIR, cntBody, readAt, ceil8Ps, WF, Writes, Prim.dst, rP, rN, rA, rCW, rQL, rT1, rT2, rKc,
    rKd, rCn5, cTmp, regs]

theorem wf_chainIR (N : ℕ) (tab : List Word) {sd : XIR} (hsd : WF sd) (hc : ¬ Writes sd rCC) :
    WF (chainIR N tab sd) := by
  refine ⟨⟨wf_cntIR, wf_storesIR _ _, hsd, by simp [startPs, WF, Prim.dst, rWp, rEo, rPi, rTl,
    rTh, rTo, rMt]⟩, ⟨by decide, by decide, by decide⟩, by decide, not_writes_wordIR_rCC N,
    wf_wordIR N⟩

theorem cost_wordIR (N t : ℕ) : cost (wordIR N) t = 176 := by
  simp only [wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stAt, stNext, ceil8Ps,
    cost, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem cost_cntIR (t : ℕ) : cost cntIR t = 13 + t / 5 * 24 := by
  simp only [cntIR, cntBody, readAt, ceil8Ps, cost, blkSteps, List.length_cons, List.length_nil,
    List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  omega

theorem cost_chainIR (N t : ℕ) (tab : List Word) (sd : XIR) :
    cost (chainIR N tab sd) t = 34 + 9 * tab.length + cost sd t + t / 5 * 24 + t * 179 := by
  simp only [chainIR, cost, cost_cntIR, cost_storesIR, cost_wordIR, startPs, blkSteps,
    List.length_cons, List.length_nil, Aff.eval, Nat.one_mul, Nat.div_one]
  norm_num
  omega

theorem sizeIR_chainIR (N : ℕ) (tab : List Word) (sd : XIR) :
    sizeIR (chainIR N tab sd) = 284 + 10 * tab.length + sizeIR sd := by
  simp only [chainIR, cntIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR, ansPs, setSPs, lastIR,
    recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stAt, stNext, ceil8Ps, startPs, sizeIR, size_storesIR, blkSteps, List.length_cons,
    List.length_nil, List.length_append]
  norm_num
  omega

theorem outs_chainIR (N t : ℕ) (tab : List Word) {sd : XIR} (hsd : outs sd t = 0) :
    outs (chainIR N tab sd) t = 0 := by
  simp [chainIR, cntIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stAt, stNext,
    outs, outs_storesIR, hsd]

end FR.X
