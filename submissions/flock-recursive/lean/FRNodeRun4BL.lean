-- New for `flock-recursive` (IMPC2 §7 step 3; track IMPC2b): the bit order of `F.ofBytes`, `natLE` and
-- `idxOfF`, the bit sources' values (`SrcV`, `StmtBits`, `PosBits`, `SrcOk`) and the register provenance
-- `riAcc` on the answer-driven run (`execA_ri`).
import FRNodeRows4AskBS
import FRNodeReadP

/-!
# Bit sources on the run

`FRNodeRows4AskB`'s bit rows tie an import or auxiliary cell to a *source* (`bitSrc`): a cell of the
bit area, or the constant zero. This module says what the sources hold and proves it on the run:

* **the bit order**: bit `j` of `F.ofBytes v` is bit `j % 8` of byte `j / 8` (`F.bit_ofBytes`); the
  same for `natLE` (`testBit_natLE`), so the halves `dlo`/`dhi` of a digest carry its bits `0 … 255`
  (`bit_dlo`, `bit_dhi`); bit `h` of `idxOfF b a i` is bit `i·b + h` of `natLE a` below `b`, else zero
  (`testBit_idxOfF`);
* **`SrcV`**: a source holds a bit (the cell is `Circ.bitF b`; the zero source only a false bit);
  **`StmtBits`** (the statement's cells hold its message bits, its tail is zero, byte 0 is the tag) and
  **`PosBits`** (an answer's cells hold its bits under the selected kind's map) are the two facts the
  decomposition rows give (`FRNodeRun4BS`);
* **`execA_ri`**: on the answer-driven run, every register's `riAcc` entry describes its value (an
  answer, an `idx` of an earlier register, a shift, a digest or byte read, a byte constant);
* **`srcOk_of`**: with `StmtBits` and `PosBits`, every bit source of a register holds the register's bit
  (`SrcOk`), on the run's final registers;
* **`selRows_ev`**: `selRows`' rows make the import cell the selected kind's source.
-/

namespace FR
open Circ RecursionFast Rev4

/-! ## Bit order -/

theorem testBit_ofLE' : ∀ (l : List UInt8) (m : ℕ), (ofLE l).testBit m = (l.getD (m / 8) 0).toNat.testBit (m % 8)
  | [], m => by simp [ofLE]
  | d :: l, m => by
    rw [ofLE_cons, show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.add_comm, Nat.testBit_two_pow_mul_add _ d.toNat_lt]
    by_cases hm : m < 8
    · simp [hm, Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
    · rw [if_neg hm, testBit_ofLE' l (m - 8), show m / 8 = (m - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show (m - 8) % 8 = m % 8 by omega]

/-- **`natLE`'s bit order**: bit `m` is bit `m % 8` of byte `m / 8`. -/
theorem testBit_natLE (a : Digest) {m : ℕ} (hm : m < 256) :
    (natLE a).testBit m = (a[m / 8]'(by omega)).toNat.testBit (m % 8) := by
  rw [Read.natLE_eq_ofLE, testBit_ofLE', List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList]

theorem natLE_lt (a : Digest) : natLE a < 2 ^ 256 := by
  rw [Read.natLE_eq_ofLE]
  have := ofLE_lt a.toList
  simpa using this

theorem testBit_natLE_ge (a : Digest) {m : ℕ} (hm : 256 ≤ m) : (natLE a).testBit m = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (natLE_lt a) (Nat.pow_le_pow_right (by norm_num) hm))

theorem B64.toBytes_get (a : B64) {k : ℕ} (hk : k < 8) : (a.toBytes[k]).toNat = a.val.toNat / 2 ^ (8 * k) % 256 := by
  interval_cases k <;> simp [B64.toBytes, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem B64.testBit_val (a : B64) {j : ℕ} (hj : j < 64) :
    a.val.toNat.testBit j = (a.toBytes[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  rw [B64.toBytes_get a (by omega), show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, decide_eq_true (Nat.mod_lt _ (by norm_num)), Bool.true_and]
  congr 1; omega

theorem F.bit_toBytes (x : F) {j : ℕ} (hj : j < 128) :
    x.bit j = (x.toBytes[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  unfold F.bit F.toBytes
  by_cases h : j < 64
  · rw [if_pos h, B64.testBit_val _ h, Vector.getElem_append_left (by omega)]
  · rw [if_neg h, B64.testBit_val _ (by omega), Vector.getElem_append_right (by omega) (by omega)]
    have e : ∀ a b (ha : a < 8) (hb : b < 8), a = b → x.c₁.toBytes[a] = x.c₁.toBytes[b] := by
      rintro _ _ _ _ rfl; rfl
    rw [e _ _ _ (by omega) (show (j - 64) / 8 = j / 8 - 8 by omega), show (j - 64) % 8 = j % 8 by omega]

/-- **`F.ofBytes`' bit order**: bit `j` is bit `j % 8` of byte `j / 8`. -/
theorem F.bit_ofBytes (v : Vector UInt8 16) {j : ℕ} (hj : j < 128) :
    (F.ofBytes v).bit j = (v[j / 8]'(by omega)).toNat.testBit (j % 8) := by
  rw [F.bit_toBytes _ hj, F.toBytes_ofBytes]

theorem bit_dlo (x : Digest) {j : ℕ} (hj : j < 128) : (dlo x).bit j = (natLE x).testBit j := by
  rw [dlo, F.bit_ofBytes _ hj, testBit_natLE _ (by omega), Vector.getElem_ofFn]

theorem bit_dhi (x : Digest) {j : ℕ} (hj : j < 128) : (dhi x).bit j = (natLE x).testBit (128 + j) := by
  rw [dhi, F.bit_ofBytes _ hj, testBit_natLE _ (by omega), Vector.getElem_ofFn]
  have e : ∀ a b (ha : a < 32) (hb : b < 32), a = b → x[a] = x[b] := by rintro _ _ _ _ rfl; rfl
  rw [e _ _ (by omega) (by omega) (show 16 + j / 8 = (128 + j) / 8 by omega), show j % 8 = (128 + j) % 8 by omega]

/-- **`idxOfF`'s bits**: bit `h` is bit `i·b + h` of `natLE a` below `b`, zero above. -/
theorem testBit_idxOfF (b : ℕ) (a : Digest) (i h : ℕ) :
    (idxOfF b a i).testBit h = (decide (h < b) && (natLE a).testBit (i * b + h)) := by
  rw [idxOfF_eq, idxOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm h]

theorem B64.eq_of_testBit {a b : B64} (h : ∀ j < 64, a.val.toNat.testBit j = b.val.toNat.testBit j) : a = b := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  congr 1
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 64
  · exact h j hj
  · have hp : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.toNat_lt hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt hp)]

/-- **An `F` element is its bits.** -/
theorem F.eq_of_bit {x y : F} (h : ∀ j < 128, x.bit j = y.bit j) : x = y := by
  obtain ⟨x₀, x₁⟩ := x; obtain ⟨y₀, y₁⟩ := y
  have h0 := fun j (hj : j < 64) => by simpa [F.bit, hj] using h j (by omega)
  have h1 := fun j (hj : j < 64) => by simpa [F.bit, show ¬ j + 64 < 64 by omega] using h (j + 64) (by omega)
  rw [B64.eq_of_testBit h0, B64.eq_of_testBit h1]

namespace N4s

/-! ## Sources and their values -/

/-- A source's value: its bit cell, or zero. -/
def srcVal (w : Asg) (π : ℕ) : Option ℕ → F
  | some c => w (bitC π c)
  | none => 0

/-- **A source holds bit `b`**: the cell is `Circ.bitF b`; the zero source holds only a false bit. -/
def SrcV (w : Asg) (π : ℕ) : Option ℕ → Bool → Prop
  | some c, b => w (bitC π c) = Circ.bitF b
  | none, b => b = false

theorem srcVal_of_srcV {w : Asg} {π : ℕ} {x : Option ℕ} {b : Bool} (h : SrcV w π x b) : srcVal w π x = Circ.bitF b := by
  cases x
  · simp only [SrcV] at h; subst h; rfl
  · exact h

/-- Bit `b` of the statement message (bit `b % 8` of its byte `b / 8`, in the proof `q`). -/
def stBit (T : BTab) (q : ByteArray) (b : ℕ) : Bool :=
  match T.st with
  | some s => (byteAt q (s.so + b / 8)).toNat.testBit (b % 8)
  | none => false

/-- **The statement's bits**: its tag byte, and every bit `stCell` places (a cell, or the zero tail). -/
def StmtBits (T : BTab) (w : Asg) (π : ℕ) (q : ByteArray) : Prop :=
  (∀ s, T.st = some s → byteAt q s.so = s.t) ∧ ∀ b x, T.stCell b = some x → SrcV w π x (stBit T q b)

/-- **The answers' bits** at kind `ι`: a cell `ansCell ι k j` holds bit `j` of entry `k`'s answer. -/
def PosBits (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (tr : Trace) : Prop :=
  ∀ k j x e, T.ansCell ι k j = some x → tr[k]? = some e → w (bitC π x) = Circ.bitF ((natLE e.2).testBit j)

/-- **Every bit source of a register holds the register's bit** (on the registers `regs`). -/
def SrcOk (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (regs : Array Val) : Prop :=
  ∀ r h x, T.bitSrc r h ι = some x → SrcV w π x ((rd regs r).toN.testBit h)

/-! ## Register provenance on the run -/

/-- **What an `RI` entry says of a register's value** `v` (`regs` the run's final registers). -/
def RIV (ι : Kind) (inp : Input) (tr : Trace) (regs : Array Val) : RI → Val → Prop
  | .none, _ => True
  | .ans k, v => ∃ e, tr[k]? = some e ∧ v = .d e.2
  | .idx a b i, v => v = .n (idxOfF (b ι) (rd regs (a ι)).toD (i ι))
  | .shr n s, v => v = .n ((rd regs n).toN >>> s ι)
  | .dig o, v => v = .d (digestAt inp.π o)
  | .pf o len, v => v = .b (inp.π.extract o (o + len))
  | .cb bs, v => v = .b bs

theorem riOf_len {impl : OpImpl} {ι : Kind} {inp : Input} {regs : Array Val} {op : Op} {vs : List Val}
    {ok : Bool} (hv : evalOp impl ι inp regs op = .vals vs ok) (k n : ℕ) : (riOf k n op).length = vs.length := by
  rw [evalOp_len hv]
  have hi := vals_item' hv
  unfold riOf
  rw [if_neg (by simp [hi])]
  cases op <;> simp only [List.length_replicate] <;> (try split) <;> (try split) <;> rfl

theorem rd_prefix {a more : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ more) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem riV_none {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val} {l : List RI} (hl : ∀ x ∈ l, x = .none)
    (j : ℕ) (v : Val) : RIV ι inp tr regs (l.getD j .none) v := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => trivial
  | some x => rw [hl x (List.mem_of_getElem? h)]; trivial

theorem riOf_ok {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {regs more : Array Val} {op : Op}
    {vs : List Val} {ok : Bool} (hv : evalOp impl ι inp regs op = .vals vs ok) (k : ℕ) {j : ℕ}
    (hj : j < vs.length) :
    RIV ι inp tr (regs ++ vs.toArray ++ more) ((riOf k regs.size op).getD j .none) (vs[j]'hj) := by
  have hi := vals_item' hv
  have hrd : ∀ i < regs.size, rd (regs ++ vs.toArray ++ more) i = rd regs i := fun i h => by
    rw [Array.append_assoc, rd_prefix h]
  cases op
  case idx a b i =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs with hg
    · simp only [List.getD_cons_zero, RIV, List.getElem_cons_zero]
      rw [hrd _ (by cases ι <;> simp_all)]
    · exact riV_none (by simp) _ _
  case shrN m s =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs with hg
    · simp only [List.getD_cons_zero, RIV, List.getElem_cons_zero]
      rw [hrd _ hg]
    · exact riV_none (by simp) _ _
  case piDigest f o =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp [riOf, Op.item?, RIV]
  case piField f o len =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp [riOf, Op.item?, RIV]
  case const c =>
    simp only [evalOp, Res.vals.injEq] at hv; obtain ⟨rfl, -⟩ := hv
    obtain rfl : j = 0 := by simp at hj; omega
    simp only [riOf, Op.item?, Option.isSome_none, Bool.false_eq_true, if_false, List.getElem_cons_zero]
    split
    · rename_i x y z hx hy hz
      split_ifs with he
      · obtain ⟨rfl, rfl⟩ := he
        simp only [List.getD_cons_zero, RIV]
        cases ι <;> assumption
      · exact riV_none (by simp) _ _
    · exact riV_none (by simp) _ _
  all_goals (rw [riOf, if_neg (by simp [hi])] <;> first | exact riV_none (by simp) _ _ | simp)

/-- **Register provenance along the answer-driven run** (`riAcc`, from ask `k` of `tr`): every entry
describes its register's value on the run's final registers. -/
theorem execA_ri {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {s' : St} {tr' : Trace} :
    ∀ (ops : List Op) (k : ℕ) (acc : Array RI) (s : St),
    execA impl ι inp ops s (tr.drop k) = some (s', tr') → acc.size = s.regs.size →
    (∀ r, RIV ι inp tr s'.regs (acc.getD r .none) (rd s'.regs r)) →
    ∀ r, RIV ι inp tr s'.regs ((riAcc k ops acc).getD r .none) (rd s'.regs r)
  | [], k, acc, s, he, _, h => by simpa [riAcc] using h
  | op :: ops, k, acc, s, he, hsz, h => by
    simp only [riAcc]
    simp only [execA] at he
    split at he
    · next vs ok hv =>
      have hi : op.item?.isSome = false := vals_item' hv
      rw [if_neg (by simp [hi])]
      obtain ⟨more, hm⟩ := execA_prefix ops _ _ he
      refine execA_ri ops k _ _ he (by simp [hsz, riOf_len hv]) fun r => ?_
      by_cases hr : r < acc.size
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hr, ← Array.getD_eq_getD_getElem?]
        exact h r
      · by_cases hr2 : r < acc.size + (riOf k acc.size op).length
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by omega)]
          have hj : r - acc.size < vs.length := by rw [← riOf_len hv k acc.size]; omega
          have hrd : rd s'.regs r = vs[r - acc.size] := by
            rw [hm, rd]; simp only at hm ⊢
            rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by omega)]
            rw [List.getElem?_toArray, ← hsz, List.getElem?_eq_getElem hj]; rfl
          rw [hrd]
          have := riOf_ok (tr := tr) (more := more) hv k hj
          rw [← hsz] at this
          simpa [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?] using
            (show RIV ι inp tr s'.regs ((riOf k acc.size op).getD (r - acc.size) .none) vs[r - acc.size] by
              rw [hm]; simpa [hsz] using this)
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
          trivial
    · next q hq =>
      have hi := ask_item hq
      rw [if_pos hi]
      rcases htr : tr.drop k with _ | ⟨⟨q', a⟩, tr0⟩
      · rw [htr] at he; cases he
      rw [htr] at he
      have hk : tr[k]? = some (q', a) := by
        have := congrArg List.head? htr
        rwa [List.head?_drop, List.head?_cons] at this
      have htr0 : tr0 = tr.drop (k + 1) := by
        rw [← List.drop_drop, htr]; rfl
      rw [htr0] at he
      obtain ⟨more, hm⟩ := execA_prefix ops _ _ he
      have hro : riOf k acc.size op = [.ans k] := by simp [riOf, hi]
      rw [hro]
      refine execA_ri ops (k + 1) _ _ he (by simp [hsz]) fun r => ?_
      by_cases hr : r < acc.size
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hr, ← Array.getD_eq_getD_getElem?]
        exact h r
      · by_cases hr2 : r = acc.size
        · subst hr2
          rw [show (acc ++ [RI.ans k].toArray).getD acc.size RI.none = RI.ans k by
            simp [Array.getD_eq_getD_getElem?]]
          refine ⟨(q', a), hk, ?_⟩
          rw [hm, rd]
          show ((s.regs.push (Val.d a)) ++ more)[acc.size]?.getD default = _
          rw [Array.getElem?_append_left (by simp; omega), hsz, Array.getElem?_push_eq]; rfl
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
          trivial

/-! ## The sources hold the registers' bits -/

theorem srcV_stBit {T : BTab} {w : Asg} {π : ℕ} {q : ByteArray} (hS : StmtBits T w π q) {s : StSpec}
    (hs : T.st = some s) {o j : ℕ} (hso : s.so ≤ o) (hj : j < 256) {x : Option ℕ}
    (hx : T.stCell (8 * (o - s.so) + j) = some x) :
    SrcV w π x ((natLE (digestAt q o)).testBit j) := by
  have h := hS.2 _ _ hx
  simp only [stBit, hs] at h
  rw [testBit_natLE _ hj, digestAt_eq]
  simp only [bytesAt, Vector.getElem_ofFn]
  rwa [show s.so + (8 * (o - s.so) + j) / 8 = o + j / 8 by omega, show (8 * (o - s.so) + j) % 8 = j % 8 by omega] at h

theorem idxSrc_ok {T : BTab} {w : Asg} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val}
    (hri : ∀ r, RIV ι inp tr regs (T.rt.getD r .none) (rd regs r)) (hS : StmtBits T w π inp.π)
    (hP : PosBits T w π ι tr) {a b i : KC ℕ} {h : ℕ} {x : Option ℕ} (hx : T.idxSrc a b i h ι = some x) :
    SrcV w π x ((idxOfF (b ι) (rd regs (a ι)).toD (i ι)).testBit h) := by
  unfold BTab.idxSrc at hx
  rw [testBit_idxOfF]
  split_ifs at hx with h24 hh
  · have hra := hri (a ι)
    split at hx
    · rename_i k hk
      rw [hk] at hra
      obtain ⟨e, he, hv⟩ := hra
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [hv, Val.toD, decide_eq_true hh, Bool.true_and]
      exact hP k _ c e hc he
    · rename_i o ho
      rw [ho] at hra
      split at hx
      · rename_i s hs
        split_ifs at hx with hg
        rw [hra, Val.toD, decide_eq_true hh, Bool.true_and]
        refine srcV_stBit hS hs hg.1 hg.2 ?_
        rwa [Nat.add_assoc] at hx
      · cases hx
    · cases hx
  · cases hx
    simp [SrcV, hh]

/-- **The sources hold the bits** (`SrcOk`) on registers whose provenance `riAcc` describes, given the
statement's and the answers' bits. -/
theorem srcOk_of {T : BTab} {w : Asg} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {regs : Array Val}
    (hri : ∀ r, RIV ι inp tr regs (T.rt.getD r .none) (rd regs r)) (hS : StmtBits T w π inp.π)
    (hP : PosBits T w π ι tr) : SrcOk T w π ι regs := by
  intro r h x hx
  unfold BTab.bitSrc at hx
  have hr := hri r
  split at hx
  · rename_i a b i hrr
    rw [hrr] at hr
    rw [show rd regs r = _ from hr, Val.toN]
    exact idxSrc_ok hri hS hP hx
  · rename_i n s hrr
    rw [hrr] at hr
    split at hx
    · rename_i a b i hn
      have hrn := hri n
      rw [hn] at hrn
      rw [show rd regs r = _ from hr, Val.toN, Nat.testBit_shiftRight, show rd regs n = _ from hrn, Val.toN,
        Nat.add_comm (s ι)]
      exact idxSrc_ok hri hS hP hx
    · cases hx
  · cases hx

/-! ## `selRows` -/

theorem ev_subN (w : Asg) (a b : Lin) : (subN a b).ev w = a.ev w - b.ev w := by
  simp only [subN, Lin.ev_append, sub_eq_add_neg]
  congr 1
  induction b with
  | nil => simp
  | cons t b ih => simp only [List.map_cons, Lin.ev_cons, ih, neg_add]; ring

theorem srcLin_ev (w : Asg) (π : ℕ) (x : Option ℕ) : (srcLin π x).ev w = srcVal w π x := by
  cases x <;> simp [srcLin, srcVal]

theorem gateS_ev {w : Asg} {P : Params} {ι : Kind} (hP : SelOk w P ι) (act : KC Bool) :
    (gateS P act).ev w = Circ.bitF (act ι) := by
  have hs := hP.2
  simp only [gateS, kinds, List.flatMap_cons, List.flatMap_nil, List.append_nil, Lin.ev_append]
  cases ι <;> cases h1 : act .L32 <;> cases h2 : act .P30 <;> cases h3 : act .N30 <;>
    simp [hs, h1, h2, h3, Circ.bitF]

/-- **`selRows`' rows make `imp` the selected kind's source.** -/
theorem selRows_ev {P : Params} {w : Asg} {ι : Kind} (hP : SelOk w P ι) {π : ℕ} {imp : Lin}
    {src : KC (Option (Option ℕ))} (h : ∀ r ∈ selRows P π imp src, r.Holds w) :
    ∃ x, src ι = some x ∧ imp.ev w = srcVal w π x := by
  unfold selRows at h
  split at h
  · rename_i a b c ha hb hc
    have hone := hP.1
    have hsrc : ∀ κ, src κ = some (match κ with | .L32 => a | .P30 => b | .N30 => c) := fun κ => by
      cases κ <;> assumption
    refine ⟨_, hsrc ι, ?_⟩
    split at h
    · rename_i h1
      have := h _ List.mem_cons_self
      simp only [Row.Holds, hone, one_mul, ev_subN, Lin.ev_nil, srcLin_ev] at this
      rw [sub_eq_zero.1 this]
      obtain ⟨rfl, rfl⟩ := h1
      cases ι <;> rfl
    · rename_i h1
      split at h
      · rename_i h2
        have := h _ List.mem_cons_self
        simp only [Row.Holds, gateS_ev hP, ev_subN, srcLin_ev] at this
        have key : ∀ (g : Bool) (A O : F), Circ.bitF g * (A - O) = imp.ev w - O → imp.ev w = if g then A else O := by
          intro g A O e; cases g
          · simp only [Circ.bitF, Bool.false_eq_true, if_false, zero_mul] at e ⊢; exact (sub_eq_zero.1 e.symm)
          · simp only [Circ.bitF, if_true, one_mul] at e ⊢; exact (sub_left_inj.1 e).symm
        have e := key _ _ _ this
        cases ι <;> simp only at e ⊢ <;> rw [e] <;> by_cases hba : b = a <;> by_cases hca : c = a <;> simp_all
      · have := h _ (List.mem_map.2 ⟨ι, by cases ι <;> simp [kinds], rfl⟩)
        simp only [Row.Holds, hP.2, if_true, one_mul, ev_subN, Lin.ev_nil, srcLin_ev] at this
        rw [sub_eq_zero.1 this]
        cases ι <;> rfl
  · exact absurd (h _ List.mem_cons_self) (failRT_not hP.1)

end N4s
end FR
