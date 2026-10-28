-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).
import FRNodeReadP
import FRXRead

/-!
# The output segments compiled: `segIR`

`FRNodeReadS.Seg` describes the words the node extractor emits, over a word source. Here a
segment is compiled to `XIR` (`segIR ap d`), with no store: every word is read from the heap by
one computed load (`ldw ap`). The source word `n` sits at the address

`addrW ap R n = R + (((n >>> 1) &&& m₁) <<< 18) + ((n >>> s₃) <<< s₄) + (n &&& 1)`

(`ap = (m₁, s₃, s₄)`): the stream words of a slot (`apS`) and its L words (`apL`) are both of this
shape over `f⁽⁰⁾`'s rows at `ob0` (`FRXOutRun`). The base offset of a segment is register
`oBd d` at nesting depth `d`; a `rep` at depth `d` counts in `oCd d` and moves the base of depth
`d + 1`.

* **`segIR_sem`**: from a state in context (`Ctx`: the heap is `M₀`'s, `oR = R`, the kind flag),
  the compiled segment appends `segOut (src M₀ ap R) κ b s` to the output, where
  `src M₀ ap R n` is the heap word at `addrW ap R n`;
* `wf_segIR`, `loK_segIR` (no store), `noLoopT_segIR`, and `ctx_segIR` (the context is kept).
-/

namespace FR.X

open RecursionFast FR.Read

/-! ## Registers -/

/-- The source index. -/ def oU : ℕ := 200
/-- The source base `R`. -/ def oR : ℕ := 201
/-- The word read or emitted. -/ def oX : ℕ := 202
/-- The load address. -/ def oAd : ℕ := 203
/-- Address scratch. -/ def oT1 : ℕ := 204
/-- Address scratch. -/ def oT2 : ℕ := 205
/-- Address scratch. -/ def oT3 : ℕ := 206
/-- Constants. -/ def oK : ℕ := 207
/-- The seed's second word. -/ def oY : ℕ := 208
/-- The kind flag (`kite`). -/ def oKF : ℕ := 209
/-- The copy counter. -/ def oCp : ℕ := 210
/-- The copy count. -/ def oNp : ℕ := 211
/-- The position counter. -/ def oSp : ℕ := 212
/-- The position count. -/ def oSn : ℕ := 213
/-- The depth counter. -/ def oSh : ℕ := 214
/-- The depth count. -/ def oShn : ℕ := 215
/-- The position's node pointer. -/ def oN : ℕ := 216
/-- The depth's node pointer. -/ def oNh : ℕ := 217
/-- The answer pointer. -/ def oA : ℕ := 218
/-- `(p mod per)·logN`. -/ def oRm : ℕ := 219
/-- `p mod per`. -/ def oRc : ℕ := 220
/-- The depth `h`. -/ def oH : ℕ := 221
/-- The bit index `m`. -/ def oM : ℕ := 222
/-- The bit. -/ def oB2 : ℕ := 223
/-- A flag. -/ def oFl : ℕ := 224
/-- A `rep`'s counter at depth `d`. -/ def oCd (d : ℕ) : ℕ := 226 + 3 * d
/-- A `rep`'s count at depth `d`. -/ def oNd (d : ℕ) : ℕ := 227 + 3 * d
/-- The base at depth `d`. -/ def oBd (d : ℕ) : ℕ := 228 + 3 * d

/-! ## Specification: the address block and the compiled segments -/

/-- An address shape `(m₁, s₃, s₄)`. -/
structure AP where
  m1 : ℕ
  s3 : ℕ
  s4 : ℕ

/-- **The address of source word `x`** from the base `R`, as the machine computes it. -/
def addrW (ap : AP) (R x : Word) : Word :=
  XOp.add.eval (XOp.add.eval (XOp.add.eval R
    (XOp.shl.eval (XOp.and.eval (XOp.shr.eval x (toWord 1)) (toWord ap.m1)) (toWord 18)))
    (XOp.shl.eval (XOp.shr.eval x (toWord ap.s3)) (toWord ap.s4))) (XOp.and.eval x 1)

/-- **The source**: word `n` is the heap word at `addrW ap R n`. -/
def src (M : Mem) (ap : AP) (R : ℕ) (n : ℕ) : Word := rd M (addrW ap (toWord R) (toWord n)).toNat

/-- The address block: `oAd := addrW ap oR oU`. -/
def ldPs (ap : AP) : List Prim :=
  [.const oK (toWord 1), .op .shr oT1 oU oK, .const oK (toWord ap.m1), .op .and oT1 oT1 oK,
   .const oK (toWord 18), .op .shl oT1 oT1 oK, .const oK (toWord ap.s3), .op .shr oT2 oU oK,
   .const oK (toWord ap.s4), .op .shl oT2 oT2 oK, .op .and oT3 oU cOne, .op .add oAd oR oT1,
   .op .add oAd oAd oT2, .op .add oAd oAd oT3]

/-- **One source word**: `oX := M[addrW ap oR oU]`. -/
def ldw (ap : AP) : XIR := .seq (.blk (ldPs ap)) (.load oX oAd)

/-- **A copy** of `n` source words from `rb + o`. -/
def cpIR (ap : AP) (rb o n : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (.loopK oCp oNp (toWord n) (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))

/-- Four zero words. -/
def zeros4 : XIR := .seq (.blk [.const oX 0]) (.seq (.out oX) (.seq (.out oX) (.seq (.out oX) (.out oX))))

/-- A sibling at a real depth: the bit `m = oRm + oH` of the answer at `oA`, then the left half
(node words 2–5) for bit `1`, the right half (6–9) for bit `0`. -/
def sibHit (ap : AP) : XIR :=
  .seq (.blk [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU])
    (.seq (ldw ap) (.seq (.blk [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne])
      (.ite oB2 (cpIR ap oNh 2 4) (cpIR ap oNh 6 4))))

/-- One depth `h`: a sibling below `sK`, zeros above; `h += 1`, the node pointer moves 14. -/
def sibH (ap : AP) (sK : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord sK), .op .ltu oFl oH oK])
    (.seq (.ite oFl (sibHit ap) zeros4) (.blk [.op .add oH oH cOne, .const oK 14, .op .add oNh oNh oK]))

/-- One position `p`: its `sS` depths, then `p + 1`: the node pointer moves `S`, `p mod per`
and `(p mod per)·logN` step, and wrap to the next answer (10 words on) at `per`. -/
def sibP (ap : AP) (S sS logN per sK : ℕ) : XIR :=
  .seq (.blk [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)])
    (.seq (.loopK oSh oShn (toWord sS) (sibH ap sK))
      (.seq (.blk [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
          .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK])
        (.ite oFl (.blk [.const oRc 0, .const oRm 0, .const oK 10, .op .add oA oA oK]) (.blk []))))

/-- **One level's siblings** (`Seg.sib`) from base register `rb`. -/
def sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
      .const oRm 0, .const oRc 0, .const oSn (toWord t)])
    (.loopK oSp oSn (toWord t) (sibP ap S sS logN per sK))

/-- **A compiled segment** at depth `d` (base register `oBd d`). -/
def segIR (ap : AP) : ℕ → Seg → XIR
  | _, .nil => .blk []
  | d, .cat x y => .seq (segIR ap d x) (segIR ap d y)
  | _, .wd x => .seq (.blk [.const oX x]) (.out oX)
  | d, .cp o n => cpIR ap (oBd d) o n
  | d, .rep c s x => .seq (.blk [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (.loopK (oCd d) (oNd d) (toWord c)
        (.seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s), .op .add (oBd (d + 1)) (oBd (d + 1)) oK])))
  | d, .shw o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.op .or oY oX oX, .op .add oU oU cOne]) (.seq (ldw ap)
        (.seq (.blk [.const oK (toWord 56), .op .shl oX oX oK, .const oK (toWord 8), .op .shr oY oY oK,
          .op .add oX oY oX])
          (.out oX)))))
  | d, .sh8 o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.const oK (toWord 8), .op .shr oX oX oK]) (.out oX)))
  | d, .kite x y => .ite oKF (segIR ap d x) (segIR ap d y)
  | d, .sib o S t sS ansW logN per sK => sibIR ap (oBd d) o S t sS ansW logN per sK

/-- The `rep` nesting depth. -/
def depthSeg : Seg → ℕ
  | .cat x y | .kite x y => max (depthSeg x) (depthSeg y)
  | .rep _ _ x => depthSeg x + 1
  | _ => 0

/-- The counts fit a word with room (`< 2^32`), and a level's `per` is positive. -/
def okSeg : Seg → Bool
  | .cat x y | .kite x y => okSeg x && okSeg y
  | .rep c _ x => decide (c < 2 ^ 32) && okSeg x
  | .cp _ n => decide (n < 2 ^ 32)
  | .sib _ _ t sS _ logN per sK => decide (t < 2 ^ 32) && decide (sS < 2 ^ 32) &&
      decide (logN < 2 ^ 32) && decide (per < 2 ^ 32) && decide (sK < 2 ^ 32) && decide (0 < per)
  | _ => true

/-- **The machine's context** for a segment: the heap is `M₀`'s, `oR = R`, the kind flag is `κ`. -/
structure Ctx (M₀ : Mem) (R : ℕ) (κ : Bool) (s : St) : Prop where
  inv : Inv s.M
  size : s.M.size = M₀.size
  heap : ∀ y, regs ≤ y → rd s.M y = rd M₀ y
  r : rd s.M oR = toWord R
  k : rd s.M oKF = 0 ↔ κ = false

/-- The registers a segment at depth `d` keeps: `oR`, `oKF`, the outer `rep`s' and its base. -/
def Prot (d r : ℕ) : Prop := r = oR ∨ r = oKF ∨ (226 ≤ r ∧ r < 226 + 3 * d) ∨ r = 228 + 3 * d

/-! ## Proof helpers: what the code writes -/

/-- The cells a program names as destinations, as a list. -/
def wrL : XIR → List ℕ
  | .blk ps => ps.map Prim.dst
  | .load d _ | .input d _ => [d]
  | .store .. => [cTmp]
  | .out _ => []
  | .seq p q | .ite _ p q => wrL p ++ wrL q
  | .loopK c _ _ b => c :: cTmp :: wrL b
  | .loopT c _ _ b => c :: wrL b

theorem writes_wrL : ∀ (P : XIR) (r : ℕ), Writes P r → r ∈ wrL P
  | .blk ps, r, ⟨p, hp, he⟩ => List.mem_map.2 ⟨p, hp, he⟩
  | .load _ _, _, h | .input _ _, _, h | .store _ _, _, h => List.mem_singleton.2 h
  | .out _, _, h => h.elim
  | .seq p q, r, h | .ite _ p q, r, h => List.mem_append.2 (h.imp (writes_wrL p r) (writes_wrL q r))
  | .loopK c _ _ b, r, h => by
    rcases h with rfl | rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (writes_wrL b r h))
  | .loopT c _ _ b, r, h => by
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (writes_wrL b r h)

/-- Leaf code writes only leaf registers (and the compiler's `cTmp`). -/
def LW (r : ℕ) : Prop := r = cTmp ∨ (200 ≤ r ∧ r ≤ 224 ∧ r ≠ 201 ∧ r ≠ 209)

/-- The registers a segment at depth `d` may write: the leaf registers, and the `rep` registers
from depth `d` on. -/
def OW (d r : ℕ) : Prop :=
  LW r ∨ ∃ e, d ≤ e ∧ (r = 226 + 3 * e ∨ r = 227 + 3 * e ∨ r = 231 + 3 * e)

theorem lw_cpIR (ap : AP) (rb o n r : ℕ) (h : Writes (cpIR ap rb o n) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [cpIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oNp, oCp, cTmp] at this ⊢; omega

theorem lw_sibIR (ap : AP) (rb o S t sS ansW logN per sK r : ℕ)
    (h : Writes (sibIR ap rb o S t sS ansW logN per sK) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [sibIR, sibP, sibH, sibHit, zeros4, cpIR, ldw, ldPs, wrL, List.map_cons, List.map_nil,
    Prim.dst, List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff,
    or_false, List.mem_append] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oNp, oCp, cTmp, oN, oA, oRm, oRc, oSn, oSp, oNh, oH,
    oShn, oSh, oFl, oM, oB2] at *; omega

theorem ow_segIR (ap : AP) : ∀ (seg : Seg) (d r : ℕ), Writes (segIR ap d seg) r → OW d r
  | .nil, _, _, h => by simp [segIR, Writes] at h
  | .cat x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .kite x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .wd _, _, r, h => by
    simp [segIR, Writes, Prim.dst] at h; exact .inl (.inr (by simp only [oX] at *; omega))
  | .cp o n, d, r, h => .inl (lw_cpIR ap _ o n r h)
  | .sib .., d, r, h => .inl (lw_sibIR ap _ _ _ _ _ _ _ _ _ r h)
  | .shw o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oY, cTmp] at *; omega
  | .sh8 o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, cTmp] at *; omega
  | .rep c s x, d, r, h => by
    simp only [segIR, Writes, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with ⟨p, hp, rfl⟩ | rfl | rfl | h | ⟨p, hp, rfl⟩
    · rcases hp with rfl | rfl
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oNd]⟩
    · exact .inr ⟨d, le_rfl, by simp [oCd]⟩
    · exact .inl (.inl rfl)
    · rcases ow_segIR ap x (d + 1) r h with h | ⟨e, he, h⟩
      · exact .inl h
      · exact .inr ⟨e, by omega, h⟩
    · rcases hp with rfl | rfl
      · exact .inl (.inr (by simp [Prim.dst, oK]))
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩

theorem not_ow_prot {d r : ℕ} (hp : Prot d r) (hw : OW d r) : False := by
  simp only [Prot, OW, LW, oR, oKF, cTmp] at hp hw
  rcases hw with h | ⟨e, he, h⟩ <;> omega

/-- **A segment keeps its protected registers.** -/
theorem noW_segIR (ap : AP) (seg : Seg) (d r : ℕ) (hp : Prot d r) : ¬ Writes (segIR ap d seg) r :=
  fun h => not_ow_prot hp (ow_segIR ap seg d r h)

/-! ## Proof helpers: well formed, no store, the context -/

theorem wf_ldw (ap : AP) : WF (ldw ap) := by
  simp [ldw, ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, oX]

theorem wf_cpIR (ap : AP) (rb o n : ℕ) : WF (cpIR ap rb o n) := by
  refine ⟨by simp [WF, Prim.dst, oK, oU, oNp], ⟨by simp [oCp, oNp, cTmp], by simp [oCp, regs], fun h => ?_,
    wf_ldw ap, trivial, by simp [WF, Prim.dst, oU]⟩⟩
  have := writes_wrL _ _ h
  simp [wrL, ldw, ldPs, Prim.dst, oCp, oK, oT1, oT2, oT3, oAd, oX, oU] at this

theorem wf_sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : WF (sibIR ap rb o S t sS ansW logN per sK) := by
  have hw : ∀ c P, (∀ r, Writes P r → r ∈ wrL P) → c ∉ wrL P → ¬ Writes P c := fun c P h hc hw => hc (h c hw)
  refine ⟨by simp [WF, Prim.dst, oK, oN, oA, oRm, oRc, oSn], ⟨by simp [oSp, oSn, cTmp], by simp [oSp, regs],
    hw _ _ (writes_wrL _) (by simp [wrL, sibP, sibH, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oSp, oK, oT1,
      oT2, oT3, oAd, oX, oU, oNp, oCp, oN, oA, oRm, oRc, oNh, oH, oShn, oSh, oFl, oM, oB2, cTmp]), ?_⟩⟩
  refine ⟨by simp [WF, Prim.dst, oNh, oH, oShn], ⟨⟨by simp [oSh, oShn, cTmp], by simp [oSh, regs],
    hw _ _ (writes_wrL _) (by simp [wrL, sibH, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oSh, oK, oT1,
      oT2, oT3, oAd, oX, oU, oNp, oCp, oNh, oH, oFl, oM, oB2, oRm, cTmp]), ?_⟩, ?_⟩⟩
  · exact ⟨by simp [WF, Prim.dst, oK, oFl], ⟨⟨by simp [WF, Prim.dst, oM, oK, oU], wf_ldw ap,
      by simp [WF, Prim.dst, oB2], wf_cpIR .., wf_cpIR ..⟩, by simp [zeros4, WF, Prim.dst, oX]⟩,
      by simp [WF, Prim.dst, oH, oK, oNh]⟩
  · exact ⟨by simp [WF, Prim.dst, oK, oN, oRm, oRc, oFl], by simp [WF, Prim.dst, oK, oA, oRc, oRm]⟩

theorem wf_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → WF (segIR ap d seg)
  | .nil, _, _ => by simp [segIR, WF]
  | .cat x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp [segIR, WF, Prim.dst, oX]
  | .cp .., _, _ => wf_cpIR ..
  | .sib .., _, _ => wf_sibIR ..
  | .shw _, _, _ => ⟨by simp [WF, Prim.dst, oK, oU], wf_ldw ap, by simp [WF, Prim.dst, oY, oU], wf_ldw ap,
      by simp [WF, Prim.dst, oK, oX, oY], trivial⟩
  | .sh8 _, _, _ => ⟨by simp [WF, Prim.dst, oK, oU], wf_ldw ap, by simp [WF, Prim.dst, oK, oX], trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    refine ⟨by simp [WF, Prim.dst, oBd, oNd]; omega, ⟨by simp [oCd, oNd, cTmp]; omega,
      by simp [oCd, regs]; omega, fun hw => ?_, wf_segIR ap x (d + 1) (by omega),
      by simp [WF, Prim.dst, oK, oBd]; omega⟩⟩
    rcases hw with hw | ⟨p, hp, he⟩
    · exact noW_segIR ap x (d + 1) _ (.inr (.inr (.inl ⟨by simp only [oCd]; omega, by simp only [oCd]; omega⟩))) hw
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp [Prim.dst, oK, oCd, oBd] at he
      all_goals omega

theorem loK_ldw (ap : AP) : LoK (ldw ap) := by
  simp [ldw, ldPs, LoK, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, regs]

theorem loK_cpIR (ap : AP) (rb o n : ℕ) : LoK (cpIR ap rb o n) :=
  ⟨by simp [LoK, Prim.dst, oK, oU, oNp, regs], by simp [oCp, regs], loK_ldw ap, trivial,
    by simp [LoK, Prim.dst, oU, regs]⟩

theorem loK_sibIR (ap : AP) (rb o S t sS ansW logN per sK : ℕ) : LoK (sibIR ap rb o S t sS ansW logN per sK) := by
  simp [sibIR, sibP, sibH, sibHit, zeros4, LoK, Prim.dst, oK, oN, oA, oRm, oRc, oSn, oSp, oNh, oH, oShn,
    oSh, oFl, oM, oU, oB2, oX, regs, loK_ldw, loK_cpIR]

theorem loK_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → LoK (segIR ap d seg)
  | .nil, _, _ => by simp [segIR, LoK]
  | .cat x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp [segIR, LoK, Prim.dst, oX, regs]
  | .cp .., _, _ => loK_cpIR ..
  | .sib .., _, _ => loK_sibIR ..
  | .shw _, _, _ => ⟨by simp [LoK, Prim.dst, oK, oU, regs], loK_ldw ap, by simp [LoK, Prim.dst, oY, oU, regs],
      loK_ldw ap, by simp [LoK, Prim.dst, oK, oX, oY, regs], trivial⟩
  | .sh8 _, _, _ => ⟨by simp [LoK, Prim.dst, oK, oU, regs], loK_ldw ap, by simp [LoK, Prim.dst, oK, oX, regs],
      trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    exact ⟨by simp [LoK, Prim.dst, oBd, oNd, regs]; omega, by simp [oCd, regs]; omega,
      loK_segIR ap x (d + 1) (by omega), by simp [LoK, Prim.dst, oK, oBd, regs]; omega⟩

theorem noLoopT_cpIR (ap : AP) (rb o n : ℕ) : NoLoopT (cpIR ap rb o n) := by
  simp [cpIR, ldw, NoLoopT]

theorem noLoopT_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), NoLoopT (segIR ap d seg)
  | .nil, _ | .wd _, _ | .shw _, _ | .sh8 _, _ => by simp [segIR, ldw, NoLoopT]
  | .cat x y, d | .kite x y, d => ⟨noLoopT_segIR ap x d, noLoopT_segIR ap y d⟩
  | .cp .., _ => noLoopT_cpIR ..
  | .sib .., _ => by simp [segIR, sibIR, sibP, sibH, sibHit, zeros4, ldw, cpIR, NoLoopT]
  | .rep c s x, d => ⟨trivial, noLoopT_segIR ap x (d + 1), trivial⟩

theorem ctx_sem {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) {P : XIR} (hL : LoK P) (hw : WF P)
    (h1 : ¬ Writes P oR) (h2 : ¬ Writes P oKF) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I P s) where
  inv := inv_sem I hw hc.inv
  size := (size_sem I P s).trans hc.size
  heap y hy := (hframeK I P s hL y hy).trans (hc.heap y hy)
  r := (frame I P s hw hc.inv oR (by simp [oR, regs]) h1).trans hc.r
  k := by rw [frame I P s hw hc.inv oKF (by simp [oKF, regs]) h2]; exact hc.k

/-- **A segment keeps the context.** -/
theorem ctx_segIR {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) (ap : AP) (seg : Seg) (d : ℕ)
    (hd : depthSeg seg + d ≤ 9) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I (segIR ap d seg) s) :=
  ctx_sem I (loK_segIR ap seg d hd) (wf_segIR ap seg d hd) (noW_segIR ap seg d _ (.inl rfl))
    (noW_segIR ap seg d _ (.inr (.inl rfl))) hc

/-! ## Proof helpers: loops that emit -/

theorem iterL_emit (I : Array Word) {b : XIR} {c K : ℕ} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    ∀ m j s, j + m ≤ K → Q j s → (iterL (semXIR I b) c m s).o.toList =
      s.o.toList ++ (List.range m).flatMap (fun i => out (j + i)) ∧ Q (j + m) (iterL (semXIR I b) c m s)
  | 0, j, s, _, h => ⟨by simp only [iterL, List.range_zero, List.flatMap_nil, List.append_nil], h⟩
  | m + 1, j, s, hm, h => by
    obtain ⟨h1, h2⟩ := hf j s (by omega) h
    obtain ⟨g1, g2⟩ := iterL_emit I Q out hf m (j + 1) _ (by omega) h2
    refine ⟨?_, by rw [show j + (m + 1) = j + 1 + m by omega]; exact g2⟩
    rw [iterL, g1, show (decS c (semXIR I b s)).o = (semXIR I b s).o from rfl, h1, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map, List.append_assoc, Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1, Nat.succ_eq_add_one, Nat.add_zero]

/-- **A counted loop that emits** `out j` in iteration `j`, under an invariant `Q`. -/
theorem loopK_emit (I : Array Word) {c n K : ℕ} {b : XIR} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (s : St) (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hK : K < 2 ^ 64)
    (hN : rd s.M n = toWord K) (h0 : Q 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    (semXIR I (.loopK c n (toWord K) b) s).o.toList = s.o.toList ++ (List.range K).flatMap out ∧
      Q K (semXIR I (.loopK c n (toWord K) b) s) := by
  have e : (rd (entryK c n (toWord K) s.M) c).toNat = K := by
    rw [entryK_count hM hc hcr hn hN, toNat_toWord hK]
  have := iterL_emit I Q out hf K 0 _ (by omega) h0
  simp only [Nat.zero_add] at this
  have e2 : semXIR I (.loopK c n (toWord K) b) s =
      iterL (semXIR I b) c K ⟨entryK c n (toWord K) s.M, s.o⟩ := by
    simp only [semXIR]; rw [e]
  rw [e2]; exact this

theorem ctx_decS {M₀ : Mem} {R : ℕ} {κ : Bool} {c : ℕ} (hc4 : 4 ≤ c) (hc : c < regs) (h1 : c ≠ oR)
    (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ (decS c s) where
  inv := inv_decS h.inv hc4
  size := (size_decS c s).trans h.size
  heap y hy := (rd_decS (by omega) s).trans (h.heap y hy)
  r := (rd_decS h1 s).trans h.r
  k := by rw [rd_decS h2]; exact h.k

theorem ctx_entryK {M₀ : Mem} {R : ℕ} {κ : Bool} {c n : ℕ} {K : Word} (hc4 : 4 < c) (hc : c < regs)
    (h1 : c ≠ oR) (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ ⟨entryK c n K s.M, s.o⟩ where
  inv := inv_entryK h.inv hc4
  size := (size_entryK ..).trans h.size
  heap y hy := (entryK_frame _ (by omega) (by simp only [cTmp, regs] at *; omega)).trans (h.heap y hy)
  r := (entryK_frame _ h1 (by simp [cTmp, oR])).trans h.r
  k := by rw [show rd (entryK c n K s.M) oKF = rd s.M oKF from entryK_frame _ h2 (by simp [cTmp, oKF])]; exact h.k

/-! ## Proof helpers: one source word -/

theorem one_cOne {M : Mem} (h : Inv M) : rd M cOne = 1 := h.2 0 (by decide)

/-- **The address block reads the source word** at `addrW ap rR rU`. -/
theorem ldw_sem (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M)
    (hA : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat) :
    rd (semXIR I (ldw ap) s).M oX = rd s.M (addrW ap (rd s.M oR) (rd s.M oU)).toNat ∧
      (semXIR I (ldw ap) s).o = s.o := by
  have hs := hM.1
  have h1 := one_cOne hM
  simp only [regs] at hs hA
  have hv : rd (runPrims (ldPs ap) s.M) oAd = addrW ap (rd s.M oR) (rd s.M oU) := by
    simp only [ldPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oT1, oT2, oT3, oAd, oX, oU, oR, cOne]; omega))
      only [rd_set_self, rd_set_ne, h1]
    simp only [addrW]
  have hh : ∀ a, regs ≤ a → rd (runPrims (ldPs ap) s.M) a = rd s.M a := fun a ha =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [ldPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [regs] at ha
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prim.dst, oK, oT1, oT2, oT3, oAd] at he <;> omega) _
  constructor
  · simp only [ldw, semXIR]
    rw [rd_set_self (by rw [size_runPrims]; simp only [oX]; omega), hv, hh _ (by simp only [regs]; omega)]
  · simp only [ldw, semXIR]

theorem nw_of {P : XIR} {i : ℕ} (h : i ∉ wrL P) : ¬ Writes P i := fun hw => h (writes_wrL P i hw)

theorem loK_blk {ps : List Prim} (h : ∀ p ∈ ps, p.dst < regs) : LoK (.blk ps) := h

theorem wf_blk' {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst) : WF (.blk ps) := h

/-- The source word at the address of a register value. -/
theorem ldw_src (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {u : ℕ}
    (hu : rd s.M oU = toWord u) :
    rd (semXIR I (ldw ap) s).M oX = src M₀ ap R u ∧ (semXIR I (ldw ap) s).o = s.o := by
  have hA' : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat := by rw [hc.r, hu]; exact hA _
  obtain ⟨h1, h2⟩ := ldw_sem I ap s hc.inv hA'
  refine ⟨?_, h2⟩
  rw [h1, hc.heap _ hA', hc.r, hu]; rfl

theorem ctx_ldw (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool} {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ (semXIR I (ldw ap) s) :=
  ctx_sem I (loK_ldw ap) (wf_ldw ap) (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oR]))
    (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oKF])) hc

theorem ldw_keep (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ [oK, oT1, oT2, oT3, oAd, oX]) : rd (semXIR I (ldw ap) s).M r = rd s.M r :=
  frame I _ s (wf_ldw ap) hM r hr (nw_of (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    simp [wrL, ldw, ldPs, Prim.dst, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, eq_comm]))

/-- **The copy loop** emits `n` source words from `b + o` (`b` in `rb`). -/
theorem cpIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) {rb o n b : ℕ} (hrb : rb ≠ oK) (hn : n < 2 ^ 64)
    (s : St) (hc : Ctx M₀ R κ s) (hb : rd s.M rb = toWord b) :
    (semXIR I (cpIR ap rb o n) s).o.toList =
      s.o.toList ++ (List.range n).map (fun j => src M₀ ap R (b + o + j)) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  have hb1 : semXIR I (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)]) s =
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ := rfl
  have r1 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oU =
      toWord (b + o) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hb, add_toWord]
  have r2 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oNp =
      toWord n := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self]
  have c1 := ctx_sem (M₀ := M₀) I (P := .blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (loK_blk (by simp [Prim.dst, oK, oU, oNp, regs])) (wf_blk' (by simp [Prim.dst, oK, oU, oNp]))
    (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oR])) (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oKF])) hc
  rw [hb1] at c1
  rw [show semXIR I (cpIR ap rb o n) s = semXIR I (.loopK oCp oNp (toWord n)
      (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ from rfl]
  generalize runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M = M1 at r1 r2 c1 ⊢
  have := loopK_emit I (c := oCp) (n := oNp) (K := n)
    (b := .seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne])))
    (fun j s' => Ctx M₀ R κ s' ∧ rd s'.M oU = toWord (b + o + j)) (fun j => [src M₀ ap R (b + o + j)])
    ⟨M1, s.o⟩ c1.inv (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oNp]) hn r2
    ⟨ctx_entryK (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR]) (by simp [oCp, oKF]) c1,
      by rw [entryK_frame _ (by simp [oCp, oU]) (by simp [oU, cTmp])]; exact r1⟩
    (fun j s' _ ⟨q1, q2⟩ => by
      obtain ⟨l1, l2⟩ := ldw_src I ap hA s' q1 q2
      have k2 := ctx_ldw I ap (s := s') q1
      have u2 := ldw_keep I ap s' q1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
      simp only [semXIR_seq]
      generalize semXIR I (ldw ap) s' = s2 at l1 l2 k2 u2 ⊢
      have hs2 := k2.inv.1
      simp only [regs] at hs2
      refine ⟨by simp [semXIR, l2, l1], ⟨ctx_decS (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR])
        (by simp [oCp, oKF]) ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
      · exact inv_runPrims (by simp [Prim.dst, oU]) k2.inv
      · simp [semXIR, k2.size]
      · intro y hy
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp only [regs, oU] at *; omega)]; exact k2.heap y hy
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oR])]; exact k2.r
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oKF])]; exact k2.k
      · rw [rd_decS (by simp [oCp, oU])]
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [oU]; omega), u2, q2, one_cOne k2.inv, add_one_toWord, Nat.add_assoc])
  rw [this.1, flatMap_single]

theorem ctx_blk {M₀ : Mem} {R : ℕ} {κ : Bool} {ps : List Prim}
    (h : ∀ p ∈ ps, 4 ≤ p.dst ∧ p.dst < regs ∧ p.dst ≠ oR ∧ p.dst ≠ oKF) {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ ⟨runPrims ps s.M, s.o⟩ :=
  ctx_sem (P := .blk ps) #[] (fun p hp => (h p hp).2.1) (fun p hp => (h p hp).1)
    (fun ⟨p, hp, he⟩ => (h p hp).2.2.1 he) (fun ⟨p, hp, he⟩ => (h p hp).2.2.2 he) hc

theorem semXIR_blk (I : Array Word) (ps : List Prim) (s : St) : semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ :=
  rfl

theorem shr_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shr.eval x (toWord k) = x >>> k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

theorem shl_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shl.eval x (toWord k) = x <<< k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

/-! ## Proof helpers: the siblings -/

theorem keep_of (I : Array Word) {P : XIR} {s : St} (hw : WF P) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ wrL P) : rd (semXIR I P s).M r = rd s.M r :=
  frame I P s hw hM r hr (nw_of h)

theorem bit_shr_word (x : Word) (k : ℕ) (hk : k < 64) :
    (x >>> k &&& 1 = 0) ↔ x.toNat / 2 ^ k % 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp

theorem succ_divmod {p per : ℕ} (hper : 0 < per) :
    (p % per + 1 = per → (p + 1) % per = 0 ∧ (p + 1) / per = p / per + 1) ∧
    (p % per + 1 ≠ per → (p + 1) % per = p % per + 1 ∧ (p + 1) / per = p / per) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < per ∧ p = r + per * q :=
    ⟨p / per, p % per, Nat.mod_lt _ hper, by rw [Nat.add_comm]; exact (Nat.div_add_mod p per).symm⟩
  have e1 : (r + per * q) % per = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have e2 : (r + per * q) / per = q := by rw [Nat.add_mul_div_left _ _ hper, Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [e1, e2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show r + per * q + 1 = 0 + per * (q + 1) by rw [← h]; ring, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ hper]
    simp
  · rw [show r + per * q + 1 = (r + 1) + per * q by ring, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ hper, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
    exact ⟨rfl, rfl⟩

/-- **A sibling at a real depth**: the bit `m = rm + h` of the answer at `a`, then the node's
right (bit `0`) or left half. -/
theorem sibHit_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {nh a rm h : ℕ}
    (hm : rm + h < 2 ^ 64) (h1 : rd s.M oNh = toWord nh) (h2 : rd s.M oA = toWord a)
    (h3 : rd s.M oRm = toWord rm) (h4 : rd s.M oH = toWord h) :
    (semXIR I (sibHit ap) s).o.toList = s.o.toList ++
      if (src M₀ ap R (a + (rm + h) / 64)).toNat / 2 ^ ((rm + h) % 64) % 2 = 0 then
        (List.range 4).map fun j => src M₀ ap R (nh + 6 + j)
      else (List.range 4).map fun j => src M₀ ap R (nh + 2 + j) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibHit, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU])
    (by simp [Prim.dst, oK, oU, oM, oR, oKF, regs]) hc
  have u1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oU =
      toWord (a + (rm + h) / 64) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oM, oRm, oH, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h2, h3, h4, add_toWord, show (6 : Word) = toWord 6 from rfl, shr_toWord hm (by norm_num), add_toWord]
    rfl
  have m1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oM =
      toWord (rm + h) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oM, oRm, oH, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h3, h4, add_toWord]
  have n1 : rd (runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK, .op .add oU oA oU] s.M) oNh =
      toWord nh := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oM, oK, oU, oNh])]; exact h1
  obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
  have c2 := ctx_ldw I ap c1
  have m2 := ldw_keep I ap _ c1.inv (r := oM) (by simp [oM, regs]) (by simp [oM, oK, oT1, oT2, oT3, oAd, oX])
  have n2 := ldw_keep I ap _ c1.inv (r := oNh) (by simp [oNh, regs]) (by simp [oNh, oK, oT1, oT2, oT3, oAd, oX])
  generalize semXIR I (ldw ap) ⟨runPrims [.op .add oM oRm oH, .const oK 6, .op .shr oU oM oK,
    .op .add oU oA oU] s.M, s.o⟩ = s2 at l1 l2 c2 m2 n2
  rw [m1] at m2; rw [n1] at n2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  have c3 := ctx_blk (ps := [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne]) (by simp [Prim.dst, oB2, oR, oKF, regs]) c2
  have bit : rd (runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M) oB2 =
      (src M₀ ap R (a + (rm + h) / 64) >>> ((rm + h) % 64)) &&& 1 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oB2, oX, oM, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, m2, one_cOne c2.inv]
    simp only [XOp.eval]; rw [toNat_toWord hm]
  have nb : rd (runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M) oNh = toWord nh := by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oB2, oNh])]; exact n2
  rw [semXIR_ite, bit]
  have ho : (⟨runPrims [.op .shr oB2 oX oM, .op .and oB2 oB2 cOne] s2.M, s2.o⟩ : St).o = s.o := l2
  by_cases hb : (src M₀ ap R (a + (rm + h) / 64)).toNat / 2 ^ ((rm + h) % 64) % 2 = 0
  · rw [if_pos ((bit_shr_word _ _ (Nat.mod_lt _ (by norm_num))).2 hb), if_pos hb,
      cpIR_sem I ap hA (by simp [oNh, oK]) (by norm_num) _ c3 nb, ho]
  · rw [if_neg (fun h' => hb ((bit_shr_word _ _ (Nat.mod_lt _ (by norm_num))).1 h')), if_neg hb,
      cpIR_sem I ap hA (by simp [oNh, oK]) (by norm_num) _ c3 nb, ho]

theorem wf_sibHit (ap : AP) : WF (sibHit ap) :=
  ⟨by simp [WF, Prim.dst, oM, oK, oU], wf_ldw ap, by simp [WF, Prim.dst, oB2], wf_cpIR .., wf_cpIR ..⟩

theorem wf_zeros4 : WF zeros4 := by simp [zeros4, WF, Prim.dst, oX]

theorem loK_sibHit (ap : AP) : LoK (sibHit ap) :=
  ⟨by simp [LoK, Prim.dst, oM, oK, oU, regs], loK_ldw ap, by simp [LoK, Prim.dst, oB2, regs], loK_cpIR .., loK_cpIR ..⟩

theorem loK_zeros4 : LoK zeros4 := by simp [zeros4, LoK, Prim.dst, oX, regs]

/-- The registers a depth step leaves alone. -/
theorem sibHit_wr : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn], r ∉ wrL (.ite oFl (sibHit ap) zeros4) := by
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oA, oRm, oN, oRc, oH, oNh, oM, oK, oU, oB2, oT1, oT2, oT3,
    oAd, oX, oNp, oCp, cTmp, oSh, oShn, oSp, oSn]

/-- **One depth step** emits `sibW`'s words for `(p, h)` and moves `h` and the node pointer. -/
theorem sibH_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {b o S ansW logN per sK p h : ℕ} (hm : p % per * logN + h < 2 ^ 64) (hh : h < 2 ^ 32) (hsK : sK < 2 ^ 32)
    (h1 : rd s.M oNh = toWord (b + o + S * p + 14 * h)) (h2 : rd s.M oA = toWord (b + ansW + 10 * (p / per)))
    (h3 : rd s.M oRm = toWord (p % per * logN)) (h4 : rd s.M oH = toWord h) :
    (semXIR I (sibH ap sK) s).o.toList = s.o.toList ++ sibW (src M₀ ap R) b o S ansW logN per sK p h ∧
      Ctx M₀ R κ (semXIR I (sibH ap sK) s) ∧
      rd (semXIR I (sibH ap sK) s).M oNh = toWord (b + o + S * p + 14 * (h + 1)) ∧
      rd (semXIR I (sibH ap sK) s).M oH = toWord (h + 1) ∧
      ∀ r ∈ [oA, oRm, oN, oRc, oSh, oShn, oSp, oSn], rd (semXIR I (sibH ap sK) s).M r = rd s.M r := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibH, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oK (toWord sK), .op .ltu oFl oH oK]) (by simp [Prim.dst, oK, oFl, oR, oKF, regs]) hc
  have f1 : rd (runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M) oFl = if h < sK then 1 else 0 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oFl, oH] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [h4]
    simp only [XOp.eval]
    by_cases e : h < sK
    · rw [if_pos ((toWord_lt_toWord (by omega) (by omega)).2 e), if_pos e]
    · rw [if_neg (fun h' => e ((toWord_lt_toWord (by omega) (by omega)).1 h')), if_neg e]
  have k1 : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn],
      rd (runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M) r = rd s.M r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact rd_runPrims_of_not_writes (by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, oK, oFl, oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn]) _
  generalize runPrims [.const oK (toWord sK), .op .ltu oFl oH oK] s.M = M1 at c1 f1 k1
  have hw2 : WF (.ite oFl (sibHit ap) zeros4) := ⟨wf_sibHit ap, wf_zeros4⟩
  have c2 := ctx_sem I (P := .ite oFl (sibHit ap) zeros4) ⟨loK_sibHit ap, loK_zeros4⟩ hw2
    (nw_of (by
      simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oR, oM, oK, oU, oB2, oT1, oT2, oT3, oAd, oX, oNp, oCp, cTmp]))
    (nw_of (by
      simp [wrL, sibHit, zeros4, cpIR, ldw, ldPs, Prim.dst, oKF, oM, oK, oU, oB2, oT1, oT2, oT3, oAd, oX, oNp, oCp,
        cTmp])) c1
  have k2 : ∀ r ∈ [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn],
      rd (semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩).M r = rd s.M r := fun r hr =>
    (keep_of I hw2 c1.inv (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [oA, oRm, oN, oRc, oH, oNh, oSh, oShn, oSp, oSn, regs]) (sibHit_wr r hr)).trans (k1 r hr)
  have o2 : (semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩).o.toList =
      s.o.toList ++ sibW (src M₀ ap R) b o S ansW logN per sK p h := by
    rw [semXIR_ite, f1]
    unfold sibW
    by_cases hh' : h < sK
    · rw [if_pos hh', if_neg (by decide), if_pos hh']
      have := sibHit_sem I ap hA ⟨M1, s.o⟩ c1 (nh := b + o + S * p + 14 * h) (a := b + ansW + 10 * (p / per))
        (rm := p % per * logN) (h := h) hm (by rw [k1 _ (by simp)]; exact h1) (by rw [k1 _ (by simp)]; exact h2)
        (by rw [k1 _ (by simp)]; exact h3) (by rw [k1 _ (by simp)]; exact h4)
      exact this
    · rw [if_neg hh', if_pos rfl, if_neg hh']
      have hx : oX < M1.size := by
        have := c1.size; have := hc.size; simp only [oX] at *; omega
      simp [zeros4, semXIR, runPrims, Prim.run, rd_set_self hx]
  generalize semXIR I (.ite oFl (sibHit ap) zeros4) ⟨M1, s.o⟩ = s2 at c2 k2 o2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  refine ⟨o2, ctx_blk (by simp [Prim.dst, oH, oK, oNh, oR, oKF, regs]) c2, ?_, ?_, fun r hr => ?_⟩
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oH, oNh] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [k2 _ (by simp), h1, show (14 : Word) = toWord 14 from rfl, add_toWord]; congr 1
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oH, oNh] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [k2 _ (by simp), h4, one_cOne c2.inv, add_one_toWord]
  · rw [rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Prim.dst, oK, oH, oNh, oA, oRm, oN, oRc, oSh, oShn, oSp, oSn]), k2 r (by simp at hr ⊢; tauto)]

theorem toWord_eq_iff {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : toWord a = toWord b ↔ a = b :=
  ⟨fun h => by rw [← toNat_toWord ha, ← toNat_toWord hb, h], fun h => h ▸ rfl⟩

/-- The sibling registers of position `p`. -/
def PosR (b o S ansW logN per p : ℕ) (M : Mem) : Prop :=
  rd M oN = toWord (b + o + S * p) ∧ rd M oA = toWord (b + ansW + 10 * (p / per)) ∧
    rd M oRm = toWord (p % per * logN) ∧ rd M oRc = toWord (p % per)

/-- **One position**: its `sS` depths' sibling words, then the registers of position `p + 1`. -/
theorem sibP_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {b o S sS ansW logN per sK p : ℕ} (hp : p < 2 ^ 32) (hsS : sS < 2 ^ 32) (hl : logN < 2 ^ 32)
    (hpr : per < 2 ^ 32) (hsK : sK < 2 ^ 32) (hper : 0 < per) (hR : PosR b o S ansW logN per p s.M) :
    (semXIR I (sibP ap S sS logN per sK) s).o.toList = s.o.toList ++
      (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p) ∧
      Ctx M₀ R κ (semXIR I (sibP ap S sS logN per sK) s) ∧
      PosR b o S ansW logN per (p + 1) (semXIR I (sibP ap S sS logN per sK) s).M := by
  obtain ⟨r1, r2, r3, r4⟩ := hR
  have hs := hc.inv.1
  simp only [regs] at hs
  have hr : p % per < per := Nat.mod_lt _ hper
  have hml : ∀ h < 2 ^ 32, p % per * logN + h < 2 ^ 64 := fun h hh => by
    have : p % per * logN ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [sibP, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)])
    (by simp [Prim.dst, oNh, oH, oShn, oR, oKF, regs]) hc
  have v1 : rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oNh =
      toWord (b + o + S * p + 14 * 0) ∧ rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oH =
      toWord 0 ∧ rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) oShn = toWord sS := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oNh, oH, oShn, oN] at *; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨?_, ?_, ?_⟩ <;> simp [or_self_eval, r1, toWord]
  have k1 : ∀ r ∈ [oA, oRm, oN, oRc], rd (runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M) r =
      rd s.M r := fun r hr => rd_runPrims_of_not_writes (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [Prim.dst, oNh, oH, oShn, oA, oRm, oN, oRc]) _
  generalize runPrims [.op .or oNh oN oN, .const oH 0, .const oShn (toWord sS)] s.M = M1 at c1 v1 k1
  -- the depths
  have L := loopK_emit I (c := oSh) (n := oShn) (K := sS) (b := sibH ap sK)
    (fun h s' => Ctx M₀ R κ s' ∧ rd s'.M oNh = toWord (b + o + S * p + 14 * h) ∧ rd s'.M oH = toWord h ∧
      ∀ r ∈ [oA, oRm, oN, oRc], rd s'.M r = rd s.M r)
    (sibW (src M₀ ap R) b o S ansW logN per sK p) ⟨M1, s.o⟩ c1.inv (by simp [oSh]) (by simp [oSh, regs])
    (by simp [oSh, oShn]) (by omega) v1.2.2
    ⟨ctx_entryK (by simp [oSh]) (by simp [oSh, regs]) (by simp [oSh, oR]) (by simp [oSh, oKF]) c1,
      by rw [entryK_frame _ (by simp [oSh, oNh]) (by simp [oNh, cTmp])]; exact v1.1,
      by rw [entryK_frame _ (by simp [oSh, oH]) (by simp [oH, cTmp])]; exact v1.2.1,
      fun r hr => by
        rw [entryK_frame _ ?_ ?_, k1 r hr]
        all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        all_goals rcases hr with rfl | rfl | rfl | rfl <;> simp [oSh, oA, oRm, oN, oRc, cTmp]⟩
    (fun h s' hh ⟨q1, q2, q3, q4⟩ => by
      obtain ⟨g1, g2, g3, g4, g5⟩ := sibH_sem I ap hA s' q1 (b := b) (o := o) (S := S) (ansW := ansW)
        (logN := logN) (per := per) (sK := sK) (p := p) (h := h) (hml h (by omega)) (by omega) hsK q2
        (by rw [q4 _ (by simp)]; exact r2) (by rw [q4 _ (by simp)]; exact r3) q3
      refine ⟨g1, ctx_decS (by simp [oSh]) (by simp [oSh, regs]) (by simp [oSh, oR]) (by simp [oSh, oKF]) g2,
        by rw [rd_decS (by simp [oSh, oNh])]; exact g3, by rw [rd_decS (by simp [oSh, oH])]; exact g4,
        fun r hr => ?_⟩
      have hr' : r ≠ oSh := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp [oSh, oA, oRm, oN, oRc]
      have hr2 : r ∈ [oA, oRm, oN, oRc, oSh, oShn, oSp, oSn] := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr ⊢
        rcases hr with h | h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
      rw [rd_decS (Ne.symm hr'), g5 r hr2, q4 r hr])
  obtain ⟨L1, L2, -, -, L5⟩ := L
  generalize semXIR I (.loopK oSh oShn (toWord sS) (sibH ap sK)) ⟨M1, s.o⟩ = s3 at L1 L2 L5
  have hs3 := L2.inv.1
  simp only [regs] at hs3
  -- the step to position `p + 1`
  have c4 := ctx_blk (ps := [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
      .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK])
    (by simp [Prim.dst, oK, oN, oRm, oRc, oFl, oR, oKF, regs]) L2
  have w4 : ∀ r ∈ [oN, oRm, oRc, oFl, oA], rd (runPrims [.const oK (toWord S), .op .add oN oN oK,
      .const oK (toWord logN), .op .add oRm oRm oK, .op .add oRc oRc cOne, .const oK (toWord per),
      .op .eq oFl oRc oK] s3.M) r =
      if r = oN then toWord (b + o + S * p + S) else if r = oRm then toWord (p % per * logN + logN)
      else if r = oRc then toWord (p % per + 1)
      else if r = oFl then (if p % per + 1 = per then 1 else 0) else toWord (b + ansW + 10 * (p / per)) := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    simp only [runPrims, List.foldl, Prim.run]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (simp only [size_set, oK, oN, oRm, oRc, oFl, oA, cOne] at *; omega)) only
      [rd_set_self, rd_set_ne, if_true, if_false, show oRm ≠ oN by decide, show oRc ≠ oN by decide,
        show oRc ≠ oRm by decide, show oFl ≠ oN by decide, show oFl ≠ oRm by decide, show oFl ≠ oRc by decide,
        show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide, show oA ≠ oFl by decide]
    · rw [L5 _ (by simp), r1, add_toWord]
    · rw [L5 _ (by simp), r3, add_toWord]
    · rw [L5 _ (by simp), r4, one_cOne L2.inv, add_one_toWord]
    · rw [L5 _ (by simp), r4, one_cOne L2.inv, add_one_toWord]
      simp only [XOp.eval]
      by_cases e : p % per + 1 = per
      · rw [if_pos ((toWord_eq_iff (by omega) (by omega)).2 e), if_pos e]
      · rw [if_neg (fun h' => e ((toWord_eq_iff (by omega) (by omega)).1 h')), if_neg e]
    · rw [L5 _ (by simp), r2]
  generalize runPrims [.const oK (toWord S), .op .add oN oN oK, .const oK (toWord logN), .op .add oRm oRm oK,
    .op .add oRc oRc cOne, .const oK (toWord per), .op .eq oFl oRc oK] s3.M = M4 at c4 w4
  have hs4 := c4.inv.1
  simp only [regs] at hs4
  obtain ⟨d1, d2⟩ := succ_divmod (p := p) hper
  rw [semXIR_ite, w4 _ (by simp)]
  simp only [show oFl ≠ oN by decide, show oFl ≠ oRm by decide, show oFl ≠ oRc by decide, if_false, if_true]
  by_cases e : p % per + 1 = per
  · rw [if_pos e, if_neg (by decide), semXIR_blk]
    obtain ⟨e1, e2⟩ := d1 e
    refine ⟨L1, ctx_blk (by simp [Prim.dst, oK, oRm, oRc, oA, oR, oKF, regs]) c4, ?_, ?_, ?_, ?_⟩ <;>
    simp only [runPrims, List.foldl, Prim.run] <;>
    simp (disch := (simp only [size_set, oK, oN, oRm, oRc, oFl, oA] at *; omega)) only [rd_set_self, rd_set_ne]
    · rw [w4 _ (by simp), if_pos rfl]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide,
        show oA ≠ oFl by decide, if_false]
      rw [show (10 : Word) = toWord 10 from rfl, add_toWord, e2]; congr 1
    · rw [e1, Nat.zero_mul]; rfl
    · rw [e1]; rfl
  · rw [if_neg e, if_pos rfl, semXIR_blk]
    obtain ⟨e1, e2⟩ := d2 e
    refine ⟨L1, ctx_blk (by simp) c4, ?_, ?_, ?_, ?_⟩ <;> simp only [runPrims, List.foldl]
    · rw [w4 _ (by simp), if_pos rfl]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oA ≠ oN by decide, show oA ≠ oRm by decide, show oA ≠ oRc by decide,
        show oA ≠ oFl by decide, if_false]
      rw [e2]
    · rw [w4 _ (by simp)]; simp only [show oRm ≠ oN by decide, if_false, if_true, e1]; congr 1; ring
    · rw [w4 _ (by simp)]; simp only [show oRc ≠ oN by decide, show oRc ≠ oRm by decide, if_false, if_true, e1]

/-- **One level's siblings** (`Seg.sib`): `sibW`'s words for every position and depth. -/
theorem sibIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s)
    {rb b o S t sS ansW logN per sK : ℕ} (hrb : rb ≠ oK ∧ rb ≠ oN) (ht : t < 2 ^ 32) (hsS : sS < 2 ^ 32)
    (hl : logN < 2 ^ 32) (hpr : per < 2 ^ 32) (hsK : sK < 2 ^ 32) (hper : 0 < per) (hb : rd s.M rb = toWord b) :
    (semXIR I (sibIR ap rb o S t sS ansW logN per sK) s).o.toList = s.o.toList ++
      (List.range t).flatMap fun p => (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [sibIR, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
      .const oRm 0, .const oRc 0, .const oSn (toWord t)]) (by simp [Prim.dst, oK, oN, oA, oRm, oRc, oSn, oR, oKF, regs]) hc
  have v1 : PosR b o S ansW logN per 0 (runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW),
      .op .add oA rb oK, .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M) ∧
      rd (runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW),
      .op .add oA rb oK, .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M) oSn = toWord t := by
    simp only [PosR, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oN, oA, oRm, oRc, oSn] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hb, add_toWord, add_toWord]
    simp [toWord]
  generalize runPrims [.const oK (toWord o), .op .add oN rb oK, .const oK (toWord ansW), .op .add oA rb oK,
    .const oRm 0, .const oRc 0, .const oSn (toWord t)] s.M = M1 at c1 v1
  have L := loopK_emit I (c := oSp) (n := oSn) (K := t) (b := sibP ap S sS logN per sK)
    (fun p s' => Ctx M₀ R κ s' ∧ PosR b o S ansW logN per p s'.M)
    (fun p => (List.range sS).flatMap (sibW (src M₀ ap R) b o S ansW logN per sK p)) ⟨M1, s.o⟩ c1.inv
    (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oSn]) (by omega) v1.2
    ⟨ctx_entryK (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oR]) (by simp [oSp, oKF]) c1, by
      obtain ⟨a1, a2, a3, a4⟩ := v1.1
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals first
        | (rw [entryK_frame _ (by simp [oSp, oN]) (by simp [oN, cTmp])]; exact a1)
        | (rw [entryK_frame _ (by simp [oSp, oA]) (by simp [oA, cTmp])]; exact a2)
        | (rw [entryK_frame _ (by simp [oSp, oRm]) (by simp [oRm, cTmp])]; exact a3)
        | (rw [entryK_frame _ (by simp [oSp, oRc]) (by simp [oRc, cTmp])]; exact a4)⟩
    (fun p s' hp ⟨q1, q2⟩ => by
      obtain ⟨g1, g2, g3⟩ := sibP_sem I ap hA s' q1 (sK := sK) (by omega) hsS hl hpr hsK hper q2
      obtain ⟨a1, a2, a3, a4⟩ := g3
      exact ⟨g1, ctx_decS (by simp [oSp]) (by simp [oSp, regs]) (by simp [oSp, oR]) (by simp [oSp, oKF]) g2,
        by rw [rd_decS (by simp [oSp, oN])]; exact a1, by rw [rd_decS (by simp [oSp, oA])]; exact a2,
        by rw [rd_decS (by simp [oSp, oRm])]; exact a3, by rw [rd_decS (by simp [oSp, oRc])]; exact a4⟩)
  exact L.1

/-- **A compiled segment emits its words** (`segOut` over the source `src M₀ ap R`). -/
theorem segIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) :
    ∀ (seg : Seg) (d b : ℕ) (s : St), okSeg seg = true → depthSeg seg + d ≤ 9 → Ctx M₀ R κ s →
      rd s.M (oBd d) = toWord b →
      (semXIR I (segIR ap d seg) s).o.toList = s.o.toList ++ segOut (src M₀ ap R) κ b seg
  | .nil, _, _, s, _, _, _, _ => by simp [segIR, segOut, semXIR_blk]
  | .cat x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    have h1 := segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
    have c1 := ctx_segIR I ap x d (by omega) hc
    have k1 : rd (semXIR I (segIR ap d x) s).M (oBd d) = toWord b :=
      (frame I _ s (wf_segIR ap x d (by omega)) hc.inv _ (by simp only [oBd, regs]; omega)
        (noW_segIR ap x d _ (.inr (.inr (.inr rfl))))).trans hb
    rw [segIR, semXIR_seq, segIR_sem I ap hA y d b _ hok.2 (by omega) c1 k1, h1, segOut, List.append_assoc]
  | .kite x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    rw [segIR, semXIR_ite, segOut]
    cases κ
    · rw [if_pos (hc.k.2 rfl), if_neg (by decide)]
      exact segIR_sem I ap hA y d b s hok.2 (by omega) hc hb
    · rw [if_neg (fun h => absurd (hc.k.1 h) (by decide)), if_pos rfl]
      exact segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
  | .wd x, _, _, s, _, _, hc, _ => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp [segIR, segOut, semXIR, runPrims, Prim.run, rd_set_self (show oX < s.M.size by simp only [oX]; omega)]
  | .cp o n, d, b, s, hok, _, hc, hb => by
    simp only [okSeg, decide_eq_true_eq] at hok
    have := cpIR_sem I ap hA (rb := oBd d) (o := o) (n := n) (b := b) (by simp [oBd, oK]; omega) (by omega) s hc hb
    rw [segIR, segOut]; exact this
  | .sib o S t sS ansW logN per sK, d, b, s, hok, _, hc, hb => by
    simp only [okSeg, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    rw [segIR, segOut]
    exact sibIR_sem I ap hA s hc (by simp only [oBd, oK, oN]; omega) h1 h2 h3 h4 h5 h6 hb
  | .shw o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    have u2 := ldw_keep I ap _ c1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2 u2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    have c3 := ctx_blk (ps := [.op .or oY oX oX, .op .add oU oU cOne]) (by simp [Prim.dst, oY, oU, oR, oKF, regs]) c2
    have u3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oU = toWord (b + o + 1) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [u2, u1, one_cOne c2.inv, add_one_toWord]
    have y3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oY = src M₀ ap R (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [l1, or_self_eval]
    obtain ⟨l4, l5⟩ := ldw_src I ap hA _ c3 u3
    have y4 := ldw_keep I ap _ c3.inv (r := oY) (by simp [oY, regs]) (by simp [oY, oK, oT1, oT2, oT3, oAd, oX])
    generalize h4 : semXIR I (ldw ap) ⟨runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M, s2.o⟩ = s4 at l4 l5 y4
    have c4 : Ctx M₀ R κ s4 := by rw [← h4]; exact ctx_ldw I ap c3
    have hs4 := c4.inv.1
    simp only [regs] at hs4
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l5, l2, segOut]
    simp (disch := (simp only [size_set, oY, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l4, y4, y3, shl_c _ _ (by norm_num), shr_c _ _ (by norm_num)]
    rfl
  | .sh8 o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l2, segOut]
    simp (disch := (simp only [size_set, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, shr_c _ _ (by norm_num)]
  | .rep c s' x, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [depthSeg] at hd
    have hs := hc.inv.1
    simp only [regs] at hs
    rw [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (by simp [Prim.dst, oBd, oNd, oR, oKF, regs]; omega) hc
    have b1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oBd (d + 1)) = toWord b := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [or_self_eval, hb]
    have n1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oNd d) = toWord c := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
    generalize runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M = M1 at c1 b1 n1 ⊢
    have := loopK_emit I (c := oCd d) (n := oNd d) (K := c)
      (b := .seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s'), .op .add (oBd (d + 1)) (oBd (d + 1)) oK]))
      (fun j s'' => Ctx M₀ R κ s'' ∧ rd s''.M (oBd (d + 1)) = toWord (b + s' * j))
      (fun j => segOut (src M₀ ap R) κ (b + s' * j) x) ⟨M1, s.o⟩ c1.inv
      (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oNd]; omega)
      (by omega) n1
      ⟨ctx_entryK (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oR]; omega)
        (by simp only [oCd, oKF]; omega) c1,
        by rw [entryK_frame _ (by simp only [oCd, oBd]; omega) (by simp only [oBd, cTmp]; omega)]; simpa using b1⟩
      (fun j s'' _ ⟨q1, q2⟩ => by
        have h1 := segIR_sem I ap hA x (d + 1) (b + s' * j) s'' hok.2 (by omega) q1 q2
        have c2 := ctx_segIR I ap x (d + 1) (by omega) q1
        have k2 : rd (semXIR I (segIR ap (d + 1) x) s'').M (oBd (d + 1)) = toWord (b + s' * j) :=
          (frame I _ s'' (wf_segIR ap x (d + 1) (by omega)) q1.inv _ (by simp only [oBd, regs]; omega)
            (noW_segIR ap x (d + 1) _ (.inr (.inr (.inr rfl))))).trans q2
        simp only [semXIR_seq, semXIR_blk]
        generalize semXIR I (segIR ap (d + 1) x) s'' = s3 at h1 c2 k2 ⊢
        have hs3 := c2.inv.1
        simp only [regs] at hs3
        refine ⟨h1, ctx_decS (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega)
          (by simp only [oCd, oR]; omega) (by simp only [oCd, oKF]; omega)
          (ctx_blk (by simp [Prim.dst, oK, oBd, oR, oKF, regs]; omega) c2), ?_⟩
        rw [rd_decS (by simp only [oCd, oBd]; omega)]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oBd, oK] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [k2, add_toWord]; congr 1; ring)
    rw [this.1, segOut]

end FR.X
