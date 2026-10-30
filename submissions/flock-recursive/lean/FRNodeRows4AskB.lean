-- G6: this module also holds the former modules `FRNodeRows4AskBL`, `FRNodeRows4AskPosT`, `FRNodeRows4AskI`, `FRNodeRows4AskT` (one section each, in import order).
import FRVIRTplCore
import FRVIRTplFast
import FRNodeRows4Ext
import FRNodeRows4ArenaPlace
import FRVerifierC4
import FRNodeKinds4
import FRVIR4Mux

section G6_FRNodeRows4AskBL

-- New for `flock-recursive` (IMPC2 §0, the design's `FRBits128`; track IMPC2): the bits of an `F`
-- element and Boolean decompositions `Σ e_j·b_j`, below the bit generator.

/-!
# Bits of `F` and Boolean decompositions

`F` is `GF(2^64)[y]` on two little-endian words and its addition is `xor`, so `Σ_j e_j·b_j` with
Boolean `b_j` and distinct `j < 128` is the element whose bit `j` is `b_j`, and the bits are unique.

* **`eBit j`**: the element with bit `j` alone (`c₀`'s bit `j`, or `c₁`'s bit `j − 64`); **`F.bit`**.
* **`bit_eBit`**, **`bit_bitsLin`**: the bits of `Σ e_j·w(c_j)`; **`decomp_cell`**: a decomposition
  row's Boolean cells are the element's bits.
-/

namespace FR
open Circ


namespace F
/-- Bit `j` of an `F` element (`j < 64`: `c₀`'s, else `c₁`'s bit `j − 64`). -/
def bit (x : F) (j : ℕ) : Bool := if j < 64 then x.c₀.val.toNat.testBit j else x.c₁.val.toNat.testBit (j - 64)

theorem bit_add (a b : F) (j : ℕ) : (a + b).bit j = (a.bit j ^^ b.bit j) := by
  change (F.add a b).bit j = _
  simp only [bit, F.add]
  split <;> simp [HAdd.hAdd, Add.add, B64.add, UInt64.toNat_xor, Nat.testBit_xor]

theorem bit_zero (j : ℕ) : (0 : F).bit j = false := by
  simp only [bit]; split <;> exact Nat.zero_testBit _
end F

/-- **The `F` element with bit `j` alone** (`j < 64`: `c₀`'s bit `j`; else `c₁`'s bit `j − 64`), the
order of `F.toBytes`' little-endian bytes. -/
def eBit (j : ℕ) : F :=
  if j < 64 then ⟨⟨(1 : UInt64) <<< j.toUInt64⟩, ⟨0⟩⟩ else ⟨⟨0⟩, ⟨(1 : UInt64) <<< (j - 64).toUInt64⟩⟩

theorem eBit_shl_toNat {j : ℕ} (hj : j < 64) : ((1 : UInt64) <<< j.toUInt64).toNat = 2 ^ j := by
  rw [UInt64.toNat_shiftLeft]
  have h1 : (j.toUInt64).toNat % 64 = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt hj]
  rw [h1, UInt64.toNat_one, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]

theorem bit_eBit {i j : ℕ} (hi : i < 128) (hj : j < 128) : (eBit i).bit j = decide (i = j) := by
  unfold eBit F.bit
  by_cases h1 : i < 64 <;> by_cases h2 : j < 64 <;> simp only [h1, h2, ite_true, ite_false]
  · rw [eBit_shl_toNat h1, Nat.testBit_two_pow]
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega
  · rw [eBit_shl_toNat (by omega), Nat.testBit_two_pow]; simp; omega

theorem bit_eBit_mul (w : Asg) (i c j : ℕ) (hi : i < 128) (hj : j < 128) (hb : w c = 0 ∨ w c = 1) :
    (eBit i * w c).bit j = (decide (i = j) && decide (w c = 1)) := by
  rcases hb with h | h <;> rw [h]
  · rw [mul_zero, F.bit_zero]; simp [show (0 : F) ≠ 1 by decide]
  · rw [mul_one, bit_eBit hi hj]; simp

/-- **The bits of `Σ e_i·w(c_i)`** over Boolean cells, distinct bit indices below 128. -/
theorem bit_bitsLin (w : Asg) : ∀ (L : List (ℕ × ℕ)), (∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1) →
    (∀ p ∈ L, p.1 < 128) → (L.map Prod.fst).Nodup → ∀ j < 128,
    (Lin.ev w (L.map fun p => (p.2, eBit p.1))).bit j = decide (∃ p ∈ L, p.1 = j ∧ w p.2 = 1)
  | [], _, _, _, j, _ => by simp [Lin.ev, F.bit_zero]
  | p :: L, hb, hL, hd, j, hj => by
    rw [List.map_cons, Lin.ev_cons, F.bit_add, bit_eBit_mul w p.1 p.2 j (hL p (by simp)) hj (hb p (by simp)),
      bit_bitsLin w L (fun q hq => hb q (by simp [hq])) (fun q hq => hL q (by simp [hq]))
        (List.nodup_cons.1 (by simpa only [List.map_cons] using hd)).2 j hj]
    have hn : p.1 ∉ L.map Prod.fst := (List.nodup_cons.1 (by simpa only [List.map_cons] using hd)).1
    by_cases hpj : p.1 = j
    · have : ¬ ∃ q ∈ L, q.1 = j ∧ w q.2 = 1 := fun ⟨q, hq, hqj, _⟩ =>
        hn (List.mem_map.2 ⟨q, hq, hqj.trans hpj.symm⟩)
      by_cases hw : w p.2 = 1 <;> simp [hpj, hw, this]
    · simp [hpj]

/-- **A Boolean decomposition determines its cells**: if `x = Σ e_i·w(c_i)` then each cell is `x`'s bit. -/
theorem decomp_cell (w : Asg) (L : List (ℕ × ℕ)) (hb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1)
    (hL : ∀ p ∈ L, p.1 < 128) (hd : (L.map Prod.fst).Nodup) {x : F}
    (hx : x = Lin.ev w (L.map fun p => (p.2, eBit p.1))) {p : ℕ × ℕ} (hp : p ∈ L) :
    w p.2 = if x.bit p.1 then 1 else 0 := by
  rw [hx, bit_bitsLin w L hb hL hd p.1 (hL p hp)]
  have : (∃ q ∈ L, q.1 = p.1 ∧ w q.2 = 1) ↔ w p.2 = 1 := by
    refine ⟨fun ⟨q, hq, hqp, hw⟩ => ?_, fun h => ⟨p, hp, rfl, h⟩⟩
    rwa [List.inj_on_of_nodup_map hd hq hp hqp] at hw
  rcases hb p hp with h | h <;> simp [this, h, show (0 : F) ≠ 1 by decide]

/-- (+) `eBit 3` has bit 3, `eBit 100` bit 100; (−) neither has a neighbouring bit. -/
theorem eBit_ctl : (eBit 3).bit 3 = true ∧ (eBit 3).bit 4 = false ∧ (eBit 100).bit 100 = true ∧
    (eBit 100).bit 99 = false := by
  simp only [bit_eBit (by norm_num : 3 < 128), bit_eBit (by norm_num : 100 < 128), (by norm_num : (4 : ℕ) < 128),
    (by norm_num : (99 : ℕ) < 128)]
  decide

end FR

end G6_FRNodeRows4AskBL

section G6_FRNodeRows4AskPosT

-- New for `flock-recursive` (PACK-4.4.1 §4.2, §5.2; IMP-RESULT §5.5; track ASK-P): the ask templates'
-- rows as a fold along the compile's trail, below `FRNodeRows4`, so that the node's M rows can hold them.

/-!
# Row generators along the compile's trail (the ask templates' rows, foldable into `nodeIRows4`)

B3's ask template `FRNodeRun4.AT` is a pair (`cov`, `rows`) and its rows are the fold `askRowsX`
along the compile's trail. Both live above `FRNodeRows4` (they import the soundness chain), so the
node's M rows cannot name them. This module restates the pair (**`TG`**) and the fold
(**`trailRows`**, `askRowsX` verbatim; `FRNodeRows4AskPosF.askRowsX_eq` proves them equal), so that
`FRNodeRows4` folds the node's template rows (`askTG`, `askRowsT`) into each slot's arena rows.

* **`trailMS`**: the same fold with the plan's template memo (`FRVIRTplBuild.compMSX`'s), accumulated
  in reverse (tail-recursive): the process start computes the rows once per prototype without
  rebuilding a template per op. **`trailMS_eq`**: it is `trailRows` (reversed onto the accumulator).
* **`inpTG X π`**: IMP's `input` template (`FRNodeRows4AskInp.AT.inp`, its rows `inpRowsT`), as a
  generator. Today's node template is it alone (`FRNodeRows4.askTG`); the other classes (ASK-T,
  IMPC) are added to `askTG` there (`TG.add`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **A row generator along the trail** (B3's `AT`: the ops it covers besides the asks, and its rows
at a compile state, the previous op and the ask counter). -/
structure TG where
  cov : Op → Bool
  rows : Params → CS → Option Op → Op → ℕ → List Row

/-- The generator with no rows, covering nothing (`AT.none`). -/
def TG.none : TG := ⟨fun _ => false, fun _ _ _ _ _ => []⟩

/-- Two generators side by side (`AT.add`). -/
def TG.add (A B : TG) : TG :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k => A.rows P cs pre op k ++ B.rows P cs pre op k⟩

/-- **The generator's rows along the trail** (`FRNodeRun4.askRowsX`): at an ask or a covered op, its
rows at the aligned state; the ask counter `k` counts the asks before. -/
def trailRows (X : Ext) (P : Params) (G : TG) : CS → Option Op → ℕ → List Op → List Row
  | _, _, _, [] => []
  | cs, pre, k, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if op.item?.isSome || G.cov op then G.rows P c pre op k else []) ++
      trailRows X P G (c.add op (stepOut X P c op)) (some op) (if op.item?.isSome then k + 1 else k) ops

/-- **The same fold with the template memo** (`compMSX`'s), the rows accumulated in reverse. -/
def trailMS (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    List (TKey × Tpl) → CS → Option Op → ℕ → List Op → List Row → List Row
  | _, _, _, _, [], acc => acc
  | M, cs, pre, k, op :: ops, acc =>
    let c := cs.align (alignOf op ops)
    let acc := (if op.item?.isSome || G.cov op then G.rows P c pre op k else []).reverseAux acc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P c op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P c op
    trailMS X L P G (memoAdd M o.tin) (c.add op o) (some op) (if op.item?.isSome then k + 1 else k) ops acc

/-- **`trailMS` is `trailRows`** (reversed onto the accumulator), for a memo of `tplOf`'s templates. -/
theorem trailMS_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (pre : Option Op) (k : ℕ) (acc : List Row),
      MOk M → trailMS X L P G M cs pre k ops acc = (trailRows (X L.ctx) P G cs pre k ops).reverse ++ acc
  | [], _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, pre, k, acc, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    simp only [trailMS, trailRows, hc]
    rw [trailMS_eq X L P G ops _ _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _), List.reverseAux_eq,
      List.reverse_append, List.append_assoc]

/-- **From a fresh state**: the rows in order. -/
theorem trailMS_T (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (base : ℕ) (ops : List Op)
    {M : List (TKey × Tpl)} (h : MOk M) :
    (trailMS X L P G M (CS.init base) none 0 ops []).reverse = trailRows (X L.ctx) P G (CS.init base) none 0 ops := by
  rw [trailMS_eq X L P G ops M _ _ _ _ h, List.append_nil, List.reverse_reverse]

/-! ## The `input` generator (IMP's `AT.inp`) -/

/-- Prototype `π`'s `input` cell `h` of digest `j` (`FRNodeRows4AskInp.inC`). -/
def inCT (π j h : ℕ) : ℕ := π * slotM4 + W4.inOff + 2 * j + h

/-- A row no assignment with `one = 1` meets (`FRNodeRows4AskInp.failR`). -/
def failRT (P : Params) : Row := ⟨P.one, P.one, []⟩

/-- **The `input j` op's rows** (`FRNodeRows4AskInp.inpRowsT`): its digest slot's two cells are the
`input` cells, else `failRT`. -/
def inpRowsG (X : Ext) (π : ℕ) (P : Params) (cs : CS) (j : ℕ) : List Row :=
  match (stepOut X P cs (.input j)).slots with
  | [some (.d, [l₀, l₁])] =>
    [⟨P.one, l₀.sub (Lin.cell (inCT π (if j = 0 then 0 else 1) 0)), []⟩,
     ⟨P.one, l₁.sub (Lin.cell (inCT π (if j = 0 then 0 else 1) 1)), []⟩]
  | _ => [failRT P]

/-- **The `input` generator** of prototype `π` (extension `X`): covers the `input` ops. -/
def inpTG (X : Ext) (π : ℕ) : TG where
  cov op := match op with | .input _ => true | _ => false
  rows P cs _ op _ := match op with | .input j => inpRowsG X π P cs j | _ => []

/-! ## The reserve generator (SRA's `AT.rsv`, `FRNodeRsvLink`) -/

/-- Reserve cell `j` (`FRNodeRsvLink.rsvC`). -/
def rsvCT (j : ℕ) : ℕ := rsvRel.getD j 0

/-- The row point's entry `j` (`FRNodeRsvLink.tauC`). -/
def tauCT (j : ℕ) : ℕ := if j < 23 then rsvCT j else rsvCT (25 + j)

/-- The column point's entry `j` (`FRNodeRsvLink.sigC`). -/
def sigCT (j : ℕ) : ℕ := rsvCT (23 + j)

/-- `l` is the cell `c` (`FRNodeRsvLink.eqRowIf`). -/
def eqRowIfT (P : Params) (l : Lin) (c : ℕ) : List Row :=
  if l = Lin.cell c then [] else [⟨P.one, l.sub (Lin.cell c), []⟩]

/-- An `F`-array operand on the cells `f 0 … f (n−1)` (`FRNodeRsvLink.argRows`). -/
def argRowsT (P : Params) (s : Slot) (n : ℕ) (f : ℕ → ℕ) : List Row :=
  match s with
  | some (.af m, ls) =>
    if m = n ∧ ls.length = n then (ls.zipIdx).flatMap (fun p => eqRowIfT P p.1 (f p.2)) else [failRT P]
  | _ => [failRT P]

/-- Three `F` outputs on `rsvCT 57 … 59` (`FRNodeRsvLink.outRows`). -/
def outRowsT (P : Params) : List Slot → List Row
  | [some (.f, [l₀]), some (.f, [l₁]), some (.f, [l₂])] =>
    eqRowIfT P l₀ (rsvCT 57) ++ eqRowIfT P l₁ (rsvCT 58) ++ eqRowIfT P l₂ (rsvCT 59)
  | _ => [failRT P]

/-- The rows at an `evalM` op (`FRNodeRsvLink.rsvRowsT`). -/
def rsvRowsG (X : Ext) (P : Params) (cs : CS) : Op → List Row
  | .evalM t s => kinds.flatMap (fun κ => argRowsT P (cs.slotK t κ) 32 tauCT ++ argRowsT P (cs.slotK s κ) 25 sigCT) ++
      outRowsT P (stepOut X P cs (.evalM t s)).slots
  | _ => []

/-- Whether an op is an `evalM`. -/
def isEvalMT : Op → Bool
  | .evalM .. => true
  | _ => false

/-- **The reserve generator** of prototype `π` (SRA's `AT.rsv X π`): at prototype 0, the `evalM` ops. -/
def rsvTG (X : Ext) (π : ℕ) : TG where
  cov op := π == 0 && isEvalMT op
  rows P cs _ op _ := if π = 0 then rsvRowsG X P cs op else []

/-! ## Controls -/

/-- (+) Along `[input 0, accept]` the `input` generator emits its two rows (the `input` op compiles to
a digest slot), (−) the empty generator none; the ask counter does not move at a non-ask. -/
theorem trailRows_ctl :
    (trailRows noExt ⟨Lin.cell 0, fun _ => []⟩ (inpTG noExt 0) (CS.init 4) none 0 [.input 0, .accept]).length = 2 ∧
    trailRows noExt ⟨Lin.cell 0, fun _ => []⟩ TG.none (CS.init 4) none 0 [.input 0, .accept] = [] :=
  ⟨rfl, rfl⟩

end Rev4
end FR

end G6_FRNodeRows4AskPosT

section G6_FRNodeRows4AskI

-- New for `flock-recursive` (PACK-4.4.1 §1.3, §5.2; IMP-RESULT §5.3; SRA-RESULT §6; track IMPC): the
-- import-class generators `impcTG` (proof fields, challenge conversions, zero pins) and `colTG`, below `FRNodeRows4`.

/-!
# The import classes' row generator (`impcTG`)

B3's `ATImp` binds a covered op's import cells to its value at the slot's input. This module gives
the rows, as a generator along the compile's trail (`FRNodeRows4AskPosT.TG`), so that `FRNodeRows4`
can fold them with the other ask templates' (`askTG π := … .add (impcTG (XofT π) π)`):

* **Proof fields at a static offset** (`piElem`, `piElemK`, `piDigest`; PACK §1.3 "proof fields
  except siblings", and (β′)'s cap-check reads of `A`, the caps and `D`): a 16-byte window of the
  proof that is one whole stream element of the slot's segment is arena₁'s cell of that element.
  **`pfLoc o`** finds which item's query byte proof byte `o` is (the field's phase part, `pSegs`, then
  the phase's shape, `phItem`), **`winE o`** the element of a window `[o, o + 16)` if its 16 bytes are
  16 consecutive query bytes of one item starting on an element boundary (outside the segment's last
  block). A covered read gets one row per `F` component, `1·(l − A₁(e)) = 0`.
* **Challenge conversions** (`chF a c`, `c < 2`, and `chK a`): the import cells are the answer
  register's own cells (`dlo`/`dhi`), read off its slot.

* **Zero pins** (SRA §6.3): at a foreign `assertZero a act` whose operand is a `piField`'s bytes
  (`provL`: the program's `piField` registers, passed in as `pv`) and whose windows are elements, each
  window's arena₁ cell is pinned, `gate act · A₁(e) = 0`.
* **`colTG`** (separate, ≈ 27.9 k rows per prototype): a `dotKF`'s `felems` auxiliary cells on the
  arena₁ cells of its column's windows.

Reads whose window is not an element (the statement's `h`/`n` at stmt bytes 1 and 33) and the
siblings (`fSibs`, the half of a node query chosen by a position bit) are not covered: they stay
residual imports.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Tables (computed once at process start) -/

/-- **Item `k`'s stream offset** `Σ_{j<k} slen_j` (in a segment, after its first byte), as a table. -/
def itOffA : Array ℕ := (((itemsOf seq4).map Item.slen).scanl (· + ·) 0).toArray

/-- `seq4`'s items, as a table. -/
def itemsA : Array Item := (itemsOf seq4).toArray

/-- `seq4`'s phases, as a table. -/
def phasesA : Array (String × Sh) := (phasesOf seq4).toArray

/-- **Phase `n`'s first item**: `Σ_{q<n} |items of phase q|`, as a table. -/
def phIxA : Array ℕ := (((phasesOf seq4).map fun p => (p.2.itemsL seq4.lv).length).scanl (· + ·) 0).toArray

/-- A field's phase part: its absolute start, length, the field and the phase. -/
structure PSeg where
  st : ℕ
  len : ℕ
  f : ℕ
  n : ℕ

/-- **The proof's phase parts** (every field `f`, every phase `n` contributing bytes to it): field `f`'s
bytes of phase `n` start at `fieldOffOf seq4 f + phaseOffOf seq4 n f` (the generators' `o f`). -/
def pSegs : List PSeg :=
  (List.range nFields4).flatMap fun f => (List.range (phasesOf seq4).length).filterMap fun n =>
    let len := ((phasesOf seq4).getD n ("", .seed)).2.bytesToL seq4.lv f
    if len = 0 then none else some ⟨fieldOffOf seq4 f + phaseOffOf seq4 n f, len, f, n⟩

/-- **Which query byte of the phase's items byte `j` of its part of field `f` is**: the item (relative
to the phase's first) and the query byte (`ctb4`'s shapes; `none` for the siblings). -/
def phItem (sh : Sh) (f j : ℕ) : Option (ℕ × ℕ) :=
  match sh with
  | .seed => if f = fHdr then some (0, 71 + j) else none
  | .absorb g _ => if f = g then some (0, 40 + j) else none
  | .uni g => if f = g then some (0, 40 + j) else none
  | .rounds g _ _ inK => if f = g then some (2 * (j / roundBytes inK), 40 + j % roundBytes inK) else none
  | .queries i =>
    if f = fCols then some ((1 + (seq4.lv i).sib) * (j / colBytes i), 8 + j % colBytes i) else none
  | .squeezes _ _ => none

/-- **Proof byte `o`'s item and query byte** (`(k, q)`: byte `q` of item `k`'s query). -/
def pfLoc (o : ℕ) : Option (ℕ × ℕ) :=
  match pSegs.find? (fun s => decide (s.st ≤ o ∧ o < s.st + s.len)) with
  | some s =>
    (phItem (phasesA.getD s.n ("", .seed)).2 s.f (o - s.st)).map fun r => (phIxA.getD s.n 0 + r.1, r.2)
  | none => none

/-- **A 16-byte proof window that is one stream element** of the slot's segment: `[o, o + 16)` are
query bytes `[q, q + 16)` of one item `k`, the window starts on an element boundary, and item `k` is
not the last block's. The element. -/
def winE (o : ℕ) : Option ℕ :=
  match pfLoc o with
  | some (k, q) =>
    let x := 1 + itOffA.getD k 0 + 8 + q
    if x % 16 = 0 ∧ k < itemsA.size ∧ q + 16 ≤ (itemsA.getD k .seed).qlen ∧
        1 + itOffA.getD k 0 + (itemsA.getD k .seed).slen + 64 ≤ N4c.segB ∧
        (List.range 16).all (fun t => pfLoc (o + t) == some (k, q + t)) = true
    then some (x / 16) else none
  | none => none

/-! ## The generator -/

/-- **A component on arena₁'s element `e`** (prototype `π`'s frame): `1·(l − A₁(e)) = 0`. -/
def a1Row (P : Params) (π : ℕ) (l : Lin) (e : ℕ) : Row := ⟨P.one, l.sub (Lin.cell (π * slotM4 + arA1 + e)), []⟩

/-- `l` equals `m`: `1·(l − m) = 0`. -/
def eqLRow (P : Params) (l m : Lin) : Row := ⟨P.one, l.sub m, []⟩

/-- **A static proof read's rows**: its `F` components on the elements of its windows. -/
def pfRows (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (os : List ℕ) : List Row :=
  match sl with
  | [some (t', ls)] =>
    if t' = t ∧ ls.length = os.length then
      (ls.zip os).flatMap fun p => match winE p.2 with
        | some e => [a1Row P π p.1 e]
        | none => [failRT P]
    else [failRT P]
  | _ => [failRT P]

/-- **A challenge conversion's rows**: its components are the answer's (a digest slot `[a₀, a₁]`, the
same at every kind): `chF a c` is `a_c`, `chK a` is `[a₀, a₁]`. -/
def chRows (P : Params) (cs : CS) (a : ℕ) (sl : List Slot) (t : Ty) (cs' : List ℕ) : List Row :=
  match cs.kslots.lookup a, cs.slot a, sl with
  | none, some (.d, [a₀, a₁]), [some (t', ls)] =>
    if t' = t ∧ ls.length = cs'.length then
      (ls.zip cs').map fun p => eqLRow P p.1 (if p.2 = 0 then a₀ else a₁)
    else [failRT P]
  | _, _, _ => [failRT P]

/-! ## Register provenance, zero pins, column words -/

/-- **The `piField` registers of an op list** from register `n`: `(r, f, o, len)` for the register `r` a
`piField f o len` appends (each op appends `Op.outs` registers). -/
def provL : ℕ → List Op → List (ℕ × ℕ × ℕ × ℕ)
  | _, [] => []
  | n, op :: ops =>
    (match op with | .piField f o len => [(n, f, o, len)] | _ => []) ++ provL (n + op.outs) ops

/-- `provL`'s fold, accumulated in reverse (tail-recursive: the process start runs it over a prototype's
≈ 155 k ops, which `provL`'s non-tail recursion overflows; ASK-T). -/
def provAcc : ℕ → List Op → List (ℕ × ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ × ℕ)
  | _, [], acc => acc
  | n, op :: ops, acc =>
    provAcc (n + op.outs) ops (match op with | .piField f o len => (n, f, o, len) :: acc | _ => acc)

/-- **`provL`, tail-recursive** (`provLT_eq`). -/
def provLT (n : ℕ) (ops : List Op) : List (ℕ × ℕ × ℕ × ℕ) := (provAcc n ops []).reverse

theorem provAcc_eq : ∀ (n : ℕ) (ops : List Op) (acc : List (ℕ × ℕ × ℕ × ℕ)),
    provAcc n ops acc = (provL n ops).reverse ++ acc
  | _, [], _ => by simp [provAcc, provL]
  | n, op :: ops, acc => by
    have ih := provAcc_eq (n + op.outs) ops
    cases op <;> simp [provAcc, provL, ih]

theorem provLT_eq (n : ℕ) (ops : List Op) : provLT n ops = provL n ops := by
  rw [provLT, provAcc_eq, List.append_nil, List.reverse_reverse]

/-- Register `r`'s `piField` (its field, offset, length), if a `piField` appended it. -/
def provOf (pv : List (ℕ × ℕ × ℕ × ℕ)) (r : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (pv.find? (·.1 == r)).map (·.2)

/-- **A byte register's windows are elements**: its bytes `[o, o + len)` of the proof are `len / 16`
whole windows `winE` accepts (`len ≡ 0 mod 16`), inside the proof. -/
def winsOk (f o len : ℕ) : Bool :=
  decide (len % 16 = 0) && decide (absOff f o + len ≤ piSizeOf seq4) &&
    (List.range (len / 16)).all fun t => (winE (absOff f o + 16 * t)).isSome

/-- **The zero pins of a foreign `assertZero a act`** whose operand is a `piField`'s bytes: each of its
windows' arena₁ cell is `0` at the active kinds (`gate act · A₁(e) = 0`). -/
def zRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (cs : CS) (a : ℕ) (act : KC Bool) : List Row :=
  match provOf pv a with
  | some (f, o, len) =>
    if a < cs.slots.size ∧ winsOk f o len = true then
      (List.range (len / 16)).filterMap fun t =>
        (winE (absOff f o + 16 * t)).map fun e => ⟨P.gate act, Lin.cell (π * slotM4 + arA1 + e), []⟩
    else []
  | none => []

/-- **A column's word cells** (`dotKF`'s auxiliary import `felems n` on register `r`, a `piField`'s
bytes): cell `b` is arena₁'s cell of window `b` (`b < len / 16`), else `0`. -/
def colRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (sz : ℕ) (cells : List Lin) (r n : ℕ) : List Row :=
  match provOf pv r with
  | some (f, o, len) =>
    if cells.length = n ∧ r < sz ∧ winsOk f o len = true then
      (cells.zipIdx).filterMap fun p =>
        if p.2 < len / 16 then (winE (absOff f o + 16 * p.2)).map fun e => a1Row P π p.1 e
        else some ⟨P.one, p.1, []⟩
    else []
  | none => []

/-- The `felems` auxiliary imports' rows (`bits` ones are not bound here). -/
def auxRows (P : Params) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (sz : ℕ) : List (List Lin × ℕ × AuxK) → List Row
  | [] => []
  | (cells, r, .felems n) :: as => colRows P π pv sz cells r n ++ auxRows P π pv sz as
  | (_, _, .bits _) :: as => auxRows P π pv sz as

/-- **The rows at an op** (prototype `π`, extension `X`, the program's `piField` registers `pv`). At an
`assertZero` or a `dotKF` (no import of their own as compiled) a failing row if the compile made them
imports. -/
def impcRows (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) (P : Params) (cs : CS) (op : Op) : List Row :=
  match op with
  | .piElem f o => pfRows P π (stepOut X P cs op).slots .f [absOff f o]
  | .piElemK f o => pfRows P π (stepOut X P cs op).slots .k [absOff f o, absOff f o + 16]
  | .piDigest f o => pfRows P π (stepOut X P cs op).slots .d [absOff f o, absOff f o + 16]
  | .chF a c => chRows P cs a (stepOut X P cs op).slots .f [c]
  | .chK a => chRows P cs a (stepOut X P cs op).slots .k [0, 1]
  | .assertZero a act => if (stepOut X P cs op).imp then [failRT P] else zRows P π pv cs a act
  | _ => []

/-- **The ops it covers**: static proof reads whose windows are elements, challenge conversions, and
(for their zero pins only) `assertZero`. -/
def impcCov : Op → Bool
  | .piElem f o => (winE (absOff f o)).isSome
  | .piElemK f o | .piDigest f o => (winE (absOff f o)).isSome && (winE (absOff f o + 16)).isSome
  | .chF _ c => decide (c < 2)
  | .chK _ => true
  | .assertZero .. => true
  | _ => false

/-- **The import-class generator** of prototype `π` (extension `X`; `pv` the program's `piField`
registers, `provL 0 (protoProg π).ops`). -/
def impcTG (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) : TG where
  cov := impcCov
  rows P cs _ op _ := impcRows X π pv P cs op

/-- Whether an op is a `dotKF`. -/
def isDotKF : Op → Bool
  | .dotKF .. => true
  | _ => false

/-- **The column-word generator** of prototype `π` (`dotKF`'s `felems` auxiliary imports on arena₁; a
failing row if the compile made the `dotKF` an import). Separate from `impcTG`: ≈ 27.9 k rows per
prototype. -/
def colTG (X : Ext) (π : ℕ) (pv : List (ℕ × ℕ × ℕ × ℕ)) : TG where
  cov := isDotKF
  rows P cs _ op _ :=
    if isDotKF op then
      if (stepOut X P cs op).imp then [failRT P] else auxRows P π pv cs.slots.size (stepOut X P cs op).aux
    else []

end Rev4
end FR

end G6_FRNodeRows4AskI

section G6_FRNodeRows4AskT

-- New for `flock-recursive` (PACK-4.4.1 §1.3, §4.2; IMP-RESULT §5 item 2; track ASK-T): the ask
-- templates' generator, below `FRNodeRows4` so that the node's M rows hold its rows.

/-!
# The ask generator: every ask's query and answer bound to arena₁

At ask `k` of a prototype's compile trail (`trailRows`), **`askRowsG`** emits rows in the prototype's
frame over arena₁ (the slot's stream elements, `FRNodeRows4AskPosF.a1_slot`):

* **the item check**: the op asks item `k` of `seq4` (`itemsT`), else one failing row;
* **the digest operands** (an absorb's or a squeeze's state, a Merkle node's halves: `dopRows`): the
  operand's two cells are the query's elements in arena₁ (element `qElT k`, from the item's stream
  offset, its length word and its tag). Where the operand's slot or the node's activity depends on
  the kind, one row per kind gated by its selector; at a kind whose depth is inactive the elements
  are zero (`nodeQF i 0 0`);
* **the seed's `vk` and `c`**: arena₁'s elements `qElT 0 … + 3` are IMP's `input` cells (`inCT`);
* **the byte operand** (the seed's `hdr`, an absorb's message, a column): no row. The previous op is
  `piField` at the item's **source** (`srcT`: the absolute offset and length of the proof bytes the
  reassembled proof takes from this item's query), and the operand is its result; else one failing
  row (`preOk`);
* **the answer**: the answer slot's two cells are arena₁'s elements `aElT k`, `aElT k + 1`.

The tags and length words need no row here: the pack rows pin every item's first element
(`FRNodeRows4Pack.wfRows`, `headRows`). The tables are closed constants built once per process.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## The byte sources -/

/-- **Phase `n`'s byte sources**, one per item (`Sh.itemsL`'s order): the absolute offset and length
of the proof bytes `reassemble4` takes from the item's query (`FRNodeRows4AskPosR`: the seed's `hdr`,
an absorb's message, a round's message, a column), `none` for an item that gives none. -/
def Sh.srcL (S : Seq) (n : ℕ) : Sh → List (Option (ℕ × ℕ))
  | .seed => [some (fieldOffOf S fHdr + phaseOffOf S n fHdr, 48)]
  | .absorb g len => [if g < nFields4 then some (fieldOffOf S g + phaseOffOf S n g, len) else none]
  | .squeezes k _ => List.replicate k none
  | .uni g => [if g < nFields4 then some (fieldOffOf S g + phaseOffOf S n g, uniBytes) else none, none]
  | .rounds g k _ inK =>
    let o := fieldOffOf S g + phaseOffOf S n g
    (List.range k).flatMap fun p =>
      [if g < nFields4 then some (o + p * roundBytes inK, roundBytes inK) else none, none]
  | .queries i =>
    let o := fieldOffOf S fCols + phaseOffOf S n fCols
    (List.range (S.lv i).t).flatMap fun p =>
      some (o + p * colBytes i, colBytes i) :: List.replicate (S.lv i).sib none

/-- **The byte sources of `S`'s items** (aligned with `itemsOf S`). -/
def srcOf (S : Seq) : List (Option (ℕ × ℕ)) := (phasesOf S).zipIdx.flatMap fun p => p.1.2.srcL S p.2

/-! ## The tables (closed constants)

They are irreducible to the elaborator: a defeq check that reaches them (through `askTG`) would
otherwise evaluate `itemsOf seq4`. Proofs read them through `FRNodeRows4AskTB.itemsT_get` etc. -/

/-- `seq4`'s items. -/
@[irreducible] def itemsT : Array Item := (itemsOf seq4).toArray

/-- Their byte sources. -/
@[irreducible] def srcT : Array (Option (ℕ × ℕ)) := (srcOf seq4).toArray

/-- Their stream offsets after the trace's first byte (`itOff`: prefix sums of the stream lengths). -/
@[irreducible] def offT : Array ℕ := ((itemsOf seq4).scanl (fun o it => o + it.slen) 0).toArray

/-- **Item `k`'s first query element** (segment-relative): past its stream offset, its length word
and its tag (the seed's `vk`, every other query's first digest). -/
def qElT (k : ℕ) (it : Item) : ℕ := (1 + offT.getD k 0 + 8 + (itemTag it).length) / 16

/-- **Item `k`'s answer's first element** (segment-relative). -/
def aElT (k : ℕ) (it : Item) : ℕ := (1 + offT.getD k 0 + 8 + it.qlen) / 16

/-! ## The rows -/

/-- Arena₁'s cell of stream element `e` in prototype `π`'s frame. -/
def arC (π e : ℕ) : ℕ := π * slotM4 + arA1 + e

/-- `one · (l − c) = 0`: the form `l` is the cell `c`. -/
def eqCR (P : Params) (l : Lin) (c : ℕ) : Row := ⟨P.one, l.sub (Lin.cell c), []⟩

/-- Nothing if `b`, else one failing row. -/
def chkR (P : Params) (b : Bool) : List Row := if b then [] else [failRT P]

/-- Active at every kind. -/
def actAll (act : KC Bool) : Bool := act .L32 && act .P30 && act .N30

/-- **A digest operand on arena₁'s elements `E`, `E + 1`** (`act`: the kinds whose query carries it;
elsewhere the elements are zero). One row per half if the operand's slot and the activity do not
depend on the kind; otherwise one row per kind and half, gated by the kind's selector (a wrong slot
shape at an active kind: the gated failing row `sel · one = 0`). -/
def dopRows (P : Params) (cs : CS) (r π E : ℕ) (act : KC Bool) : List Row :=
  if actAll act && decide (cs.slotK r .P30 = cs.slotK r .L32) && decide (cs.slotK r .N30 = cs.slotK r .L32) then
    match cs.slotK r .L32 with
    | some (.d, [l₀, l₁]) => [eqCR P l₀ (arC π E), eqCR P l₁ (arC π (E + 1))]
    | _ => [failRT P]
  else kinds.flatMap fun κ =>
    if act κ then
      match cs.slotK r κ with
      | some (.d, [l₀, l₁]) =>
        [⟨P.sel κ, l₀.sub (Lin.cell (arC π E)), []⟩, ⟨P.sel κ, l₁.sub (Lin.cell (arC π (E + 1))), []⟩]
      | _ => [⟨P.sel κ, P.one, []⟩]
    else [⟨P.sel κ, Lin.cell (arC π E), []⟩, ⟨P.sel κ, Lin.cell (arC π (E + 1)), []⟩]

/-- **The answer** on arena₁'s elements `E`, `E + 1` (the ask's digest slot). -/
def ansRowsT (X : Ext) (P : Params) (cs : CS) (op : Op) (π E : ℕ) : List Row :=
  match (stepOut X P cs op).slots with
  | [some (.d, [l₀, l₁])] => [eqCR P l₀ (arC π E), eqCR P l₁ (arC π (E + 1))]
  | _ => [failRT P]

/-- **The byte operand `m` is the previous `piField`'s result, read at item `k`'s source.** -/
def preOk (cs : CS) (pre : Option Op) (m k : ℕ) : Bool :=
  match pre with
  | some (.piField f o len) => decide (m + 1 = cs.slots.size) && decide (srcT[k]? = some (some (absOff f o, len)))
  | _ => false

/-- **The rows at ask `k`** (prototype `π`, extension `X`). -/
def askRowsG (X : Ext) (π : ℕ) (P : Params) (cs : CS) (pre : Option Op) (op : Op) (k : ℕ) : List Row :=
  match op.item? with
  | none => []
  | some it =>
    if itemsT[k]? = some it then
      let q := qElT k it
      (match op with
        | .askSeed h =>
          chkR P (preOk cs pre h k) ++
            (List.range 4).map fun j => eqCR P (Lin.cell (arC π (q + j))) (inCT π (j / 2) (j % 2))
        | .askAbsorb st m _ => chkR P (preOk cs pre m k) ++ dopRows P cs st π q fun _ => true
        | .askSqueeze st => dopRows P cs st π q fun _ => true
        | .askNode _ _ l r act => dopRows P cs l π q act ++ dopRows P cs r π (q + 2) act
        | .askCol _ c => chkR P (preOk cs pre c k)
        | _ => []) ++
        ansRowsT X P cs op π (aElT k it)
    else [failRT P]

/-- **The ask generator** of prototype `π` (extension `X`): rows at every ask, covering no other op. -/
def askTGT (X : Ext) (π : ℕ) : TG := ⟨fun _ => false, askRowsG X π⟩

end Rev4
end FR

end G6_FRNodeRows4AskT

section G6_FRNodeRows4AskB

-- New for `flock-recursive` (IMPC2 §0–§4, PACK-4.4.1 §5.2; track IMPC2): the shared bit area's rows
-- (position bits, statement bits) and the generator `bitTG`, below `FRNodeRows4`.

/-!
# The bit area and its generator (`bitTG`)

The import cells of a position bit, a sibling, a `tensorW`'s `bits 20` and an unaligned statement
read are free M cells, and a bit of an `F` element is not `F`-linear. This module gives them Boolean
cells: the slot's **bit area** (`FRNodeRows4ArenaPlace`'s `arBt`, Boolean by `bitRows4`), laid out
(relative to `arBt`) as

* **positions** `[0, nPos)`, position-major and kind-free: bit `h` of position `p` of level `i` is
  `posCell i p h = posB i + p·logN*ᵢ + h` (`logN*ᵢ` at `m* = 32`, the largest);
* **spares** `[nPos, nPos + spareN)`: the answer bits no position uses, numbered per kind (the kinds
  share the range: one is selected);
* **statement bits** `[stmtB, stmtB + 8·(z − 1))`: bits `8 … 8z − 1` of the statement message
  (bytes `1 … z − 1`; byte `0` is the tag and bytes `≥ z` the zero tail, both constants).

**Decomposition rows** (once, at the seed's ask): each P2 answer half (arena₁'s element
`aElT k + c`) is `Σ_{j<128} e_j·cell(j)` under each kind's map (`ansCell`), gated by the kinds that
map alike; each statement element is its constant part plus `Σ e_j·cell(j)`. `e_j` (`eBit`) is the
`F` element with bit `j` alone, so Boolean cells are exactly the element's bits.

**Per-op rows** (`bitRowsOp`):

* a **sibling** read (`piDigest` in a `fSibs` part, `sibLoc`): `b·(l − r) = sib − r` per half, `b`
  the position bit, `l`, `r` the node query's halves on arena₁ (`qElT`); `sib = 0` at the kinds whose
  depth is inactive;
* an **unaligned statement read** (`stmtWins`): each 16-byte window is `Σ e_i·s(·)`;
* after a **`bitOf r h`** (at the following `selectHalf`, whose bit operand it is): the import cell is
  the bit's source (`bitSrc`: through the `idx`/`shrN` provenance to an answer's or the statement's
  bit cell, or zero);
* a **`tensorW`**'s `bits n` auxiliary cells: bit `i` of its index register, the same way.

Kind-dependent sources become one copy row, one product row (two classes) or one gated row per kind
(`selRows`). Everything is computed from the prototype's op list and its kind group (tables built
once per prototype, `BTab`); a check that fails gives a failing row, never a decision over the program.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Bits of `F` -/

/-- `eBit`'s table (`j < 128`). -/
@[irreducible] def eBitT : Array F := ((List.range 128).map eBit).toArray

/-- `Σ e_j · cell` over `(j, cell)` pairs (absolute cells). -/
def bitsLin (cs : List (ℕ × ℕ)) : Lin := cs.map fun p => (p.2, eBitT.getD p.1 0)

/-- `a − b` without a product per term (`Lin.sub`'s value: `F`'s negation is the identity). -/
def subN (a b : Lin) : Lin := a ++ b.map fun t => (t.1, -t.2)

/-- **The tag element**: byte `0` is `t`, the rest zero. -/
def tagF (t : UInt8) : F := ⟨⟨t.toUInt64⟩, ⟨0⟩⟩

/-! ## The position layout (kind-free) -/

/-- `seq4`'s levels (at `m*`). -/
@[irreducible] def lvT : Array Level := ((List.range nLevels).map seq4.lv).toArray

/-- **Level `i`'s first position cell** (relative): `Σ_{i'<i} tᵢ'·logN*ᵢ'`. -/
@[irreducible] def posBT : Array ℕ :=
  (((List.range nLevels).map fun i => (seq4.lv i).t * (seq4.lv i).logN).scanl (· + ·) 0).toArray

/-- **Bit `h` of position `p` of level `i`** (relative to the bit area). -/
def posCell (i p h : ℕ) : ℕ := posBT.getD i 0 + p * (lvT.getD i ⟨0, 1, 0, 0⟩).logN + h

/-- The position cells' count. -/
def nPos : ℕ := posBT.getD nLevels 0

/-! ## The tables of a prototype -/

/-- **What made a register** (the provenance the bit sources follow). -/
inductive RI where
  | none
  /-- The answer of ask `k`. -/
  | ans (k : ℕ)
  | idx (a b i : KC ℕ)
  | shr (n : ℕ) (s : KC ℕ)
  /-- A digest read at absolute offset `o`. -/
  | dig (o : ℕ)
  /-- A byte read `[o, o + len)`. -/
  | pf (o len : ℕ)
  /-- A byte constant. -/
  | cb (bs : ByteArray)
  deriving Inhabited

/-- The entries op `op` appends (the ask counter `k`, the register count `n`): an `idx`/`shrN` only on
earlier registers, a byte constant only if it is the same at every kind (the run proofs read them). -/
def riOf (k n : ℕ) (op : Op) : List RI :=
  if op.item?.isSome then [.ans k] else
  match op with
  | .idx a b i => if a .L32 < n ∧ a .P30 < n ∧ a .N30 < n then [.idx a b i] else [.none]
  | .shrN m s => if m < n then [.shr m s] else [.none]
  | .piDigest f o => [.dig (absOff f o)]
  | .piField f o len => [.pf (absOff f o) len]
  | .const c => match c .L32, c .P30, c .N30 with
    | .b x, .b y, .b z => if x = y ∧ x = z then [.cb x] else [.none]
    | _, _, _ => [.none]
  | op => List.replicate op.outs .none

/-- **The provenance array**: entry `r` says what made register `r` (tail-recursive). -/
def riAcc : ℕ → List Op → Array RI → Array RI
  | _, [], acc => acc
  | k, op :: ops, acc => riAcc (if op.item?.isSome then k + 1 else k) ops (acc ++ (riOf k acc.size op).toArray)

/-- The kind's index in `kinds`. -/
def kix : Kind → ℕ
  | .L32 => 0 | .P30 => 1 | .N30 => 2

/-- **The statement's layout** read off the program: its offset `so` and tag `t` (the `assertEq` of a
1-byte `piField` and a 1-byte constant), its zero tail from byte `z` to its end `L` (the `assertZero`
of a `piField` starting inside it). -/
structure StSpec where
  so : ℕ
  t : UInt8
  z : ℕ
  L : ℕ

/-- The tag's `(offset, byte)`. -/
def tagScan (rt : Array RI) : List Op → Option (ℕ × UInt8)
  | [] => none
  | .assertEq a b _ :: ops =>
    match rt.getD a .none, rt.getD b .none with
    | .pf o 1, .cb bs => if bs.size = 1 then some (o, bs.get! 0) else tagScan rt ops
    | _, _ => tagScan rt ops
  | _ :: ops => tagScan rt ops

/-- The zero tail `(start, length)` of a statement at `so`. -/
def tailScan (rt : Array RI) (so : ℕ) : List Op → Option (ℕ × ℕ)
  | [] => none
  | .assertZero a _ :: ops =>
    match rt.getD a .none with
    | .pf o len => if so < o ∧ o < so + 128 then some (o, len) else tailScan rt so ops
    | _ => tailScan rt so ops
  | _ :: ops => tailScan rt so ops

/-- **A prototype's bit tables** (built once per prototype). -/
structure BTab where
  /-- The provenance array. -/
  rt : Array RI
  /-- Each kind's ladder (`kix`, then the level). -/
  lv : Array (Array Level)
  /-- Item `k`'s answer place, if a P2 answer: level, index in its phase, global answer index. -/
  ans : Array (Option (ℕ × ℕ × ℕ))
  /-- Each kind's first spare (relative to the spare range) per global answer index. -/
  sp : Array (Array ℕ)
  /-- The spare range's size (the kinds' maximum). -/
  spN : ℕ
  /-- The statement's layout. -/
  st : Option StSpec

/-- Kind `ι`'s level `i`. -/
def BTab.lvl (T : BTab) (ι : Kind) (i : ℕ) : Level := (T.lv.getD (kix ι) #[]).getD i ⟨0, 1, 0, 0⟩

/-- **The answer bits positions use** (answer `q` of a level at ladder `K`): `min(per, t − q·per)`
positions of `logN` bits. -/
def usedBits (K : Level) (q : ℕ) : ℕ := Nat.min K.per (K.t - q * K.per) * K.logN

/-- The P2 answers' places: `(item, level, index)` in item order. -/
@[irreducible] def ansList : List (ℕ × ℕ × ℕ) :=
  (List.range (phasesOf seq4).length).flatMap fun n =>
    match ((phasesOf seq4).getD n ("", .seed)).2 with
    | .squeezes k (.pos i) => (List.range k).map fun q => (phIxA.getD n 0 + q, i, q)
    | _ => []

/-- The spares of one kind's answers, in order (`0` for an answer the kind does not use). -/
def spareL (lv : Array Level) : List ℕ :=
  ansList.map fun a =>
    let K := lv.getD a.2.1 ⟨0, 1, 0, 0⟩
    if a.2.2 < K.sq then 256 - usedBits K a.2.2 else 0

/-- **The tables** of a prototype (its op list `ops`, its kind group `G`). -/
def mkTab (ops : List Op) (G : Grp) : BTab :=
  let rt := riAcc 0 ops #[]
  let lv : Array (Array Level) :=
    (kinds.map fun ι => ((List.range nLevels).map fun i => seq4.lvK (G ι).d.m i).toArray).toArray
  let al := ansList
  let ans := (al.zipIdx.foldl (fun (a : Array (Option (ℕ × ℕ × ℕ))) p =>
      a.set! p.1.1 (some (p.1.2.1, p.1.2.2, p.2)))
    (Array.replicate (itemsOf seq4).length none))
  let sl := lv.toList.map spareL
  let sp := (sl.map fun l => (l.scanl (· + ·) 0).toArray).toArray
  let spN := (sl.map List.sum).foldl Nat.max 0
  let st := (tagScan rt ops).bind fun p =>
    (tailScan rt p.1 ops).map fun q => ⟨p.1, p.2, q.1 - p.1, q.1 + q.2 - p.1⟩
  ⟨rt, lv, ans, sp, spN, st⟩

/-! ## Cells -/

/-- The statement bits' first cell (relative): after the positions and the spares. -/
def BTab.stmtB (T : BTab) : ℕ := nPos + T.spN

/-- **Bit `j` of answer item `k` at kind `ι`** (relative cell): its position's bit, or a spare;
`none` if the kind does not use the answer or `j ≥ 256`. -/
def BTab.ansCell (T : BTab) (ι : Kind) (k j : ℕ) : Option ℕ :=
  match T.ans.getD k none with
  | some (i, q, g) =>
    let K := T.lvl ι i
    if q < K.sq ∧ j < 256 then
      let u := usedBits K q
      if j < u then some (posCell i (q * K.per + j / K.logN) (j % K.logN))
      else some (nPos + (T.sp.getD (kix ι) #[]).getD g 0 + (j - u))
    else none
  | none => none

/-- **Statement bit `b`** (bit `b % 8` of byte `b / 8` of the message): its cell (`some (some c)`),
the constant zero of the tail (`some none`), or `none` (the tag byte, or outside the message). -/
def BTab.stCell (T : BTab) (b : ℕ) : Option (Option ℕ) :=
  match T.st with
  | some s =>
    if 8 ≤ b ∧ b < 8 * s.z then some (some (T.stmtB + (b - 8)))
    else if 8 * s.z ≤ b ∧ b < 8 * s.L then some none else none
  | none => none

/-- **The source of bit `h` of the `N` value an `idx a b i` makes** (at kind `ι`): zero above its
`b` bits, else bit `i·b + h` of the digest it indexes (a P2 answer's cell or a statement cell). -/
def BTab.idxSrc (T : BTab) (a b i : KC ℕ) (h : ℕ) (ι : Kind) : Option (Option ℕ) :=
  if b ι ≤ 24 then
    if h < b ι then
      match T.rt.getD (a ι) .none with
      | .ans k => (T.ansCell ι k (i ι * b ι + h)).map some
      | .dig o =>
        match T.st with
        | some s => if s.so ≤ o ∧ i ι * b ι + h < 256 then T.stCell (8 * (o - s.so) + i ι * b ι + h) else none
        | none => none
      | _ => none
    else some none
  else none

/-- **The source of bit `h` of register `r`** at kind `ι`: an `idx`'s, or a `shrN` of an `idx` (bit
`h + s` of it). -/
def BTab.bitSrc (T : BTab) (r h : ℕ) (ι : Kind) : Option (Option ℕ) :=
  match T.rt.getD r .none with
  | .idx a b i => T.idxSrc a b i h ι
  | .shr n s =>
    match T.rt.getD n .none with
    | .idx a b i => T.idxSrc a b i (h + s ι) ι
    | _ => none
  | _ => none

/-! ## Rows -/

/-- The bit area's cell `c` (relative) in prototype `π`'s frame. -/
def bitC (π c : ℕ) : ℕ := π * slotM4 + arBt + c

/-- A source's form: the cell, or zero. -/
def srcLin (π : ℕ) : Option ℕ → Lin
  | some c => Lin.cell (bitC π c)
  | none => []

/-- `Σ_{κ : act κ} sel_κ` (no zero terms). -/
def gateS (P : Params) (act : KC Bool) : Lin := kinds.flatMap fun κ => if act κ then P.sel κ else []

/-- **`imp` is the selected kind's source**: one copy row if the kinds agree; one product row
`g_A·(a − b) = imp − b` for two classes (`A` the kinds with `L32`'s source); one gated row per kind
otherwise; a failing row if a kind has none. -/
def selRows (P : Params) (π : ℕ) (imp : Lin) (src : KC (Option (Option ℕ))) : List Row :=
  match src .L32, src .P30, src .N30 with
  | some a, some b, some c =>
    let v : KC (Option ℕ) := fun ι => match ι with | .L32 => a | .P30 => b | .N30 => c
    if b = a ∧ c = a then [⟨P.one, subN imp (srcLin π a), []⟩]
    else if b = a ∨ c = a ∨ b = c then
      let o := if b = a then c else b
      [⟨gateS P fun ι => decide (v ι = a), subN (srcLin π a) (srcLin π o), subN imp (srcLin π o)⟩]
    else kinds.map fun ι => ⟨P.sel ι, subN imp (srcLin π (v ι)), []⟩
  | _, _, _ => [failRT P]

/-- **An answer half's decomposition rows**: per class of kinds with the same map (the kinds using
the answer), `g·(A₁(e) − Σ_{j<128} e_j·cell(128c + j)) = 0`. -/
def ansRows (T : BTab) (P : Params) (π k : ℕ) (e c : ℕ) : List Row :=
  -- each kind's map once (`kt`: the three values computed before the closure)
  let m := kt fun ι => (List.range 128).map fun j => T.ansCell ι k (128 * c + j)
  let ok := kt fun ι => (m ι).all Option.isSome
  let lin := fun ι => subN (Lin.cell (arC π e))
    (bitsLin ((m ι).zipIdx.filterMap fun p => p.1.map fun x => (p.2, bitC π x)))
  let cls : List Kind := kinds.filter fun ι => ok ι && !(kinds.any fun κ => decide (kix κ < kix ι) && ok κ &&
    decide (m κ = m ι))
  (if kinds.all fun ι => (m ι).all fun x => x.all (· < arNb) then [] else [failRT P]) ++
  cls.map fun ι =>
    let g := kinds.filter fun κ => ok κ && decide (m κ = m ι)
    if g.length = 3 then ⟨P.one, lin ι, []⟩ else ⟨gateS P fun κ => g.contains κ, lin ι, []⟩

/-- Statement element `k`'s bit cells: `(j, cell)` for each bit `128k + j` a cell takes. -/
def stCells (T : BTab) (π k : ℕ) : List (ℕ × ℕ) :=
  (List.range 128).filterMap fun j =>
    match T.stCell (128 * k + j) with
    | some (some x) => some (j, bitC π x)
    | _ => none

/-- **Statement element `k`'s row**: `A₁(e) = c·one + Σ e_j·cell` (its constant part `c`: the tag at
byte `0`; the tail is zero). -/
def stElRow (T : BTab) (P : Params) (π : ℕ) (s : StSpec) (k : ℕ) : Row :=
  match winE (s.so + 16 * k) with
  | some e =>
    ⟨P.one, subN (Lin.cell (arC π e)) (bitsLin (stCells T π k)), if k = 0 then P.one.smul (tagF s.t) else []⟩
  | none => failRT P

/-- **The decomposition rows** (once per prototype): every P2 answer's halves, every statement
element (a failing row without a statement, or if the cells overflow the bit area). -/
def globRows (T : BTab) (P : Params) (π : ℕ) : List Row :=
  (ansList.flatMap fun a =>
    match itemsT[a.1]? with
    | some it => ansRows T P π a.1 (aElT a.1 it) 0 ++ ansRows T P π a.1 (aElT a.1 it + 1) 1
    | none => [failRT P]) ++
  match T.st with
  | some s =>
    (if 1 ≤ s.z ∧ s.z ≤ s.L ∧ s.L % 16 = 0 ∧ T.stmtB + 8 * s.z ≤ arNb + 8 then [] else [failRT P]) ++
      (List.range (s.L / 16)).map (stElRow T P π s)
  | none => [failRT P]

/-- **A sibling read's place**: `(level, position, depth, node item)` of the `fSibs` byte `o` (a
32-byte boundary of a queries phase's sibling part). -/
def sibLoc (o : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match pSegs.find? (fun s => decide (s.f = fSibs ∧ s.st ≤ o ∧ o < s.st + s.len)) with
  | some s =>
    match ((phasesA.getD s.n ("", .seed)).2) with
    | .queries i =>
      let sib := (lvT.getD i ⟨0, 1, 0, 0⟩).sib
      let d := o - s.st
      if d % 32 = 0 ∧ 0 < sib then
        let p := d / 32 / sib; let h := d / 32 % sib
        some (i, p, h, phIxA.getD s.n 0 + (1 + sib) * p + 1 + h)
      else none
    | _ => none
  | none => none

/-- **A sibling's rows**: per half `c`, `b·(A₁(l_c) − A₁(r_c)) = sib_c − A₁(r_c)` (`b` the position
bit), and `g·sib_c = 0` at the kinds whose depth `h` is inactive. -/
def sibRows (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (i p h k : ℕ) : List Row :=
  match itemsT[k]?, sl with
  | some (.node i' h'), [some (.d, [s₀, s₁])] =>
    if i' = i ∧ h' = h then
      let q := qElT k (.node i h)
      let b := Lin.cell (bitC π (posCell i p h))
      let ina : KC Bool := fun ι => decide ((T.lvl ι i).sib ≤ h)
      let pr := fun (s : Lin) (c : ℕ) =>
        (⟨b, subN (Lin.cell (arC π (q + c))) (Lin.cell (arC π (q + 2 + c))),
          subN s (Lin.cell (arC π (q + 2 + c)))⟩ : Row)
      [pr s₀ 0, pr s₁ 1] ++
        (if kinds.any ina then [⟨gateS P ina, s₀, []⟩, ⟨gateS P ina, s₁, []⟩] else [])
    else [failRT P]
  | _, _ => [failRT P]

/-- **An unaligned statement read's windows** (absolute offset `o`, `n` windows): inside the message
past its tag, not on an element boundary. -/
def BTab.stWin (T : BTab) (o n : ℕ) : Bool :=
  match T.st with
  | some s => decide (s.so < o ∧ o + 16 * n ≤ s.so + s.L ∧ (o - s.so) % 16 ≠ 0)
  | none => false

/-- **An unaligned statement read's rows**: window `c`'s form is `Σ_{i<128} e_i·s(8(o + 16c − so) + i)`. -/
def stRdRows (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (o n : ℕ) : List Row :=
  match T.st, sl with
  | some s, [some (t', ls)] =>
    if t' = t ∧ ls.length = n then
      (ls.zipIdx).map fun p =>
        let b0 := 8 * (o + 16 * p.2 - s.so)
        let src := (List.range 128).map fun j => (j, T.stCell (b0 + j))
        if src.all (·.2.isSome) then
          ⟨P.one, subN p.1 (bitsLin (src.filterMap fun x => match x.2 with
            | some (some c) => some (x.1, bitC π c) | _ => none)), []⟩
        else failRT P
    else [failRT P]
  | _, _ => [failRT P]

/-- An unaligned statement window's bit cells, from statement bit `b0`. -/
def rdCells (T : BTab) (π b0 : ℕ) : List (ℕ × ℕ) :=
  (List.range 128).filterMap fun j =>
    match T.stCell (b0 + j) with
    | some (some c) => some (j, bitC π c)
    | _ => none

/-- Every bit of the window from statement bit `b0` has a source. -/
def rdOk (T : BTab) (b0 : ℕ) : Bool := (List.range 128).all fun j => (T.stCell (b0 + j)).isSome

/-- **An unaligned statement read's rows** (`stRdRows` with the cells named, `bitTGS`'s). -/
def stRdRowsS (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (t : Ty) (o n : ℕ) : List Row :=
  match T.st, sl with
  | some s, [some (t', ls)] =>
    if t' = t ∧ ls.length = n then
      (ls.zipIdx).map fun p =>
        if rdOk T (8 * (o + 16 * p.2 - s.so)) then
          ⟨P.one, subN p.1 (bitsLin (rdCells T π (8 * (o + 16 * p.2 - s.so)))), []⟩
        else failRT P
    else [failRT P]
  | _, _ => [failRT P]

/-- **The `bits n` auxiliary cells' rows**: cell `i` is bit `i` of the register (an earlier one: below
the register count `m`; `n` cells). -/
def auxBRows (T : BTab) (P : Params) (π m : ℕ) : List (List Lin × ℕ × AuxK) → List Row
  | [] => []
  | (cells, r, .bits n) :: as =>
    (if r < m ∧ cells.length = n then cells.zipIdx.flatMap fun p => selRows P π p.1 (T.bitSrc r p.2)
      else [failRT P]) ++ auxBRows T P π m as
  | (_, _, .felems _) :: as => auxBRows T P π m as

/-- Whether an op is a `tensorW`. -/
def isTensorW : Op → Bool
  | .tensorW .. => true
  | _ => false

/-- **The reads `bitTGR` covers** (`ATImp` classes): sibling reads, unaligned statement reads. -/
def bitCovR (T : BTab) : Op → Bool
  | .piDigest f o => (sibLoc (absOff f o)).isSome || T.stWin (absOff f o) 2
  | .piElem f o => T.stWin (absOff f o) 1
  | .piElemK f o => T.stWin (absOff f o) 2
  | _ => false

/-- **The ops `bitTGB` covers**: every `selectHalf` (its rows only after a `bitOf`) and every
`tensorW`; neither is an import as compiled, so `ATImp` holds there vacuously. -/
def bitCovB : Op → Bool
  | .selectHalf .. => true
  | .tensorW .. => true
  | _ => false

/-- **The reads' rows** (`bitTGR`). -/
def bitRowsR (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (_ : Option Op) (op : Op) (_ : ℕ) :
    List Row :=
  match op with
  | .piDigest f o =>
    match sibLoc (absOff f o) with
    | some (i, p, h, kk) => sibRows T P π (stepOut X P cs op).slots i p h kk
    | none => if T.stWin (absOff f o) 2 then stRdRows T P π (stepOut X P cs op).slots .d (absOff f o) 2 else []
  | .piElem f o => if T.stWin (absOff f o) 1 then stRdRows T P π (stepOut X P cs op).slots .f (absOff f o) 1 else []
  | .piElemK f o => if T.stWin (absOff f o) 2 then stRdRows T P π (stepOut X P cs op).slots .k (absOff f o) 2 else []
  | _ => []

/-- **The bits' rows** (`bitTGB`): the decomposition rows at the seed's ask; after a `bitOf`, at the
following `selectHalf`, its import cell on the bit's source; a `tensorW`'s `bits` auxiliary cells. A
covered op the compile made an import gets a failing row. -/
def bitRowsB (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (pre : Option Op) (op : Op) (k : ℕ) :
    List Row :=
  match op with
  | .askSeed _ => if k = 0 then globRows T P π else []
  | .selectHalf b _ _ =>
    -- the extension alone (`opOut`'s `selectHalf` is never an import): no mux built per op
    if ((X P cs op).map Out.imp).getD false then [failRT P] else
    match pre with
    | some (.bitOf r h) =>
      match cs.slot b with
      | some (.bit, [l]) =>
        if b + 1 = cs.slots.size ∧ r < b then selRows P π l (T.bitSrc r h) else [failRT P]
      | _ => [failRT P]
    | _ => []
  | .tensorW .. =>
    if (stepOut X P cs op).imp then [failRT P] else auxBRows T P π cs.slots.size (stepOut X P cs op).aux
  | _ => []

/-- **The statement reads `bitTGS` covers** (`ATImp` class): the unaligned statement reads. -/
def bitCovS (T : BTab) : Op → Bool
  | .piDigest f o => T.stWin (absOff f o) 2
  | .piElem f o => T.stWin (absOff f o) 1
  | .piElemK f o => T.stWin (absOff f o) 2
  | _ => false

/-- **The statement reads' rows** (`bitTGS`). -/
def bitRowsS (T : BTab) (X : Ext) (π : ℕ) (P : Params) (cs : CS) (_ : Option Op) (op : Op) (_ : ℕ) :
    List Row :=
  match op with
  | .piDigest f o => if T.stWin (absOff f o) 2 then stRdRowsS T P π (stepOut X P cs op).slots .d (absOff f o) 2 else []
  | .piElem f o => if T.stWin (absOff f o) 1 then stRdRowsS T P π (stepOut X P cs op).slots .f (absOff f o) 1 else []
  | .piElemK f o => if T.stWin (absOff f o) 2 then stRdRowsS T P π (stepOut X P cs op).slots .k (absOff f o) 2 else []
  | _ => []

/-- **The bit tables of a prototype** (its op list, its kind group): `mkTab`, built once. -/
def bitTab (ops : List Op) (G : Grp) : BTab := mkTab ops G

/-- **The bits' generator** (decomposition, `bitOf`, `bits n`) of prototype `π`. `X` is the compile's
extension **with a template-free context** (`trailMS`'s key context): the rows read `imp`, `aux` and
the slots of imports, none of which depends on a template's body; building a `tensorW` template per op
costs ≈ 0.8 s per prototype at process start (`logs/IMPC2/bitstat-cls.log`). -/
def bitTGB (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovB, bitRowsB T X π⟩

/-- **The reads' generator** (siblings, unaligned statement reads) of prototype `π`. -/
def bitTGR (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovR T, bitRowsR T X π⟩

/-- **The statement reads' generator** (the unaligned statement reads of `bitTGR`, without the
siblings: IMPC2b's phase 2a) of prototype `π`. -/
def bitTGS (X : Ext) (π : ℕ) (T : BTab) : TG := ⟨bitCovS T, bitRowsS T X π⟩

/-- **Two generators side by side, each consulted only at its own ops** (its covered ops and the
asks): `B`'s covered reads (a sibling, an unaligned statement read) are reads `A`'s rows refuse when
asked (`impcTG`'s `pfRows`), and `A` is not asked there. `B.cov` is evaluated once per op, `A.cov`
only at `B`'s ops (`trailRows` asks for rows only at a covered op or an ask). -/
def TG.addD (A B : TG) : TG :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k =>
    if B.cov op then
      B.rows P cs pre op k ++ (if A.cov op || op.item?.isSome then A.rows P cs pre op k else [])
    else A.rows P cs pre op k ++ (if op.item?.isSome then B.rows P cs pre op k else [])⟩

/-- **`trailRows` of `addD` at the ops either covers is `add`'s with each side asked only there**: in
particular, if `B` covers nothing `A` refuses, the fold is unchanged on `A`'s side (`addD_none`). -/
theorem addD_none (A : TG) : (A.addD TG.none).cov = A.cov := by
  funext op; simp [TG.addD, TG.none]

/-- **Both** (the RESULT's `askTG` diff folds them one after the other). -/
def bitTG (X : Ext) (π : ℕ) (ops : List Op) (G : Grp) : TG :=
  let T := bitTab ops G
  (bitTGB X π T).addD (bitTGR X π T)

end Rev4
end FR

end G6_FRNodeRows4AskB
