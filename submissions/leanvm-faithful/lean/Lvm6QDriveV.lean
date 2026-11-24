-- New for lvm6 (WP CA2). CA's plan-driven program `drive6` (`Lvm6QPlan`) against V1's executable
-- verifier `VS6` (`Lvm6VDrive`): one direction of the link, by a step simulation over the schedule.
import Lvm6QFormat
import Lvm6QDrive
import Lvm6VDrive
import Lvm6P18Memo

/-!
# CA's driver accepts ⇒ V1's `VS6` accepts (CA2)

**`accOf sh π tr`**: V1's driver transcript (`NV`, newest first) as a pure function of the proof `π` and
the trace `tr`: the driver's primitives run with every answer read from the trace (`PA`), with no check.

**`vs6_of_drive6`**: if `drive6 (planOf sh) c π F'` accepts the trace `tr`, and `F'` (when it holds) gives
the header check, every grind (`PowOK6`) and `F π (accOf sh π tr)`, then `VS6 (toV sh) F vk c π` accepts
`tr`, for every shape whose static facts hold (`simOK`, decided by the kernel at `P18`: `simOK_P18`).

The proof is a simulation over WP-S's schedule (`sim_walk`). Between two items, CA's state (the walk
state `w`, the cursor `off`, the rest of the plan accepted from entry `w.i`: `DFut`) and V1's driver state
`ns` are related by `QRel`: the chain state is the answer of entry `w.st`; V1 has read the `w.pend` pending
bytes from `off` on (its buffer); V1's cap `l` sits at a `π` offset whose bytes are those of entry `ce`'s
query at `co` (CA's settled caps) or at `off + po` (pending caps); after level `l`'s position group, V1's
positions are the plan's (`posAll`, from the group's first entry `i0`). Each item then asks the same
queries in both programs, and V1's checks hold: bounds (the cursor of an accepted run ends at `|π|`),
`queryCap` (every planned query fits), the grinds (`PowOK6`, `pw_of_powOK`), the cap comparisons (CA's
`postOK` on the last node of each path).

The static facts (`simOK`): CA's walk is well formed (`walkOK`); every planned query fits `queryCap`;
caps are read in level order and each opening follows its level's position group (`sOK`); and the
levels of the two descriptions agree (`levOK`: height, cap, leaf bytes, openings, position draws).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay

/-! ## The driver's transcript as a pure function of `π` and the trace -/

/-- A pure driver state: V1's `NS` and the index of the next trace entry. -/
abbrev AS : Type := V.NS × ℕ

/-- A read of `w` bytes (V1's `rd`, no bounds check). -/
def aRd (π : ByteArray) (w : ℕ) (ns : V.NS) : V.NS :=
  { ns with off := ns.off + w, buf := ns.buf ++ π.extract ns.off (ns.off + w), acc := .rd ns.off w :: ns.acc,
            nr := ns.nr + 1 }

/-- A draw with answer `a` (V1's `draw`, no check). -/
def aDraw (upd : List ℕ → ℕ → List ℕ) (a : Digest) (ns : V.NS) : V.NS :=
  { ns with st := a, buf := ByteArray.empty, ps := upd ns.ps (answerBits a), acc := .draw a :: ns.acc }

/-- A cap of a commitment of `2^ht` rows of `w` words (V1's `cap`, no check). -/
def aCap (π : ByteArray) (L : List V.Lev) (ht w : ℕ) (ns : V.NS) : V.NS :=
  { ns with off := ns.off + 32 * 2 ^ V.capOfL L ht w,
            buf := ns.buf ++ π.extract ns.off (ns.off + 32 * 2 ^ V.capOfL L ht w),
            caps := ns.caps ++ [(ns.off, ht, w)], acc := .cap ht w :: ns.acc }

/-- The bytes of one opening (leaf and siblings) of a commitment of `2^ht` rows of `w` words. -/
def opnB (L : List V.Lev) (ht w : ℕ) : ℕ := 8 * min (V.occL L ht w) w + 32 * (ht - V.capOfL L ht w)

/-- The openings of commitment `i` at the current positions (V1's `opn`, no check). -/
def aOpn (L : List V.Lev) (i ht w : ℕ) (ns : V.NS) : V.NS :=
  { ns with off := ns.off + ns.ps.length * opnB L ht w,
            acc := .rows i ns.ps w (V.occL L ht w) (8 * min (V.occL L ht w) w)
              ((List.range ns.ps.length).map fun j => ns.off + j * opnB L ht w) :: ns.acc }

/-- **V1's primitives, answers read from the trace** (no check). -/
def PA (π : ByteArray) (L : List V.Lev) (tr : Trace) : V.Prims (AS → AS) where
  skip := id
  seq := fun f g s => g (f s)
  rd := fun w s => (aRd π w s.1, s.2)
  draw := fun _ upd s => (aDraw upd (aOf tr s.2) s.1, s.2 + 1)
  cap := fun ht w s => (aCap π L ht w s.1, s.2)
  reset := fun s => ({ s.1 with ps := [] }, s.2)
  opn := fun i s =>
    match s.1.caps[i]? with
    | none => s
    | some (_, ht, w) => (aOpn L i ht w s.1, s.2 + s.1.ps.length * (1 + (ht - V.capOfL L ht w)))

/-- V1's driver state after the seed (`VS6`): cursor at `|HDR|`, chain state `st`. -/
def ns0 (sh : Lvm6.Shape) (st : Digest) : V.NS := ⟨Lvm6.hdrLen sh, ByteArray.empty, st, [], [], [], 0⟩

/-- **The transcript `VS6`'s decision reads** (`F π acc`), as a function of `π` and the trace: the
schedule's primitives from entry 2 (after `q₀` and the seed), every answer the trace's. -/
def accOf (sh : Lvm6.Shape) (π : ByteArray) (tr : Trace) : List V.NV :=
  ((PA π sh.levs tr).walk sh.levs (Lvm6.sched6 sh) (ns0 sh (aOf tr 1), 2)).1.acc

/-! ## The static facts -/

/-- The simulation's static state: CA's walk state and the last position group (its first entry, its
level). -/
abbrev SS : Type := WS6 × Option (ℕ × ℕ)

/-- One item's static check (`n` levels): a cap is the next level in order; an opening's positions are
the last position group's, of its level. -/
def sstep (lv : ℕ → Lv) (n : ℕ) (s : SS) (it : Lvm6.Item) : Bool × SS :=
  match it with
  | .cap i => (i == s.1.caps.length + s.1.pcaps.length && decide (i < n), ((walk lv s.1 (itOfs lv it)).2, s.2))
  | .pos i _ => (decide (i < n), ((walk lv s.1 (itOfs lv it)).2, some (s.1.i, i)))
  | .open i => (decide (i < n) && s.2 == some (s.1.i - 1 - (lv i).gap - ((lv i).d - 1), i),
      ((walk lv s.1 (itOfs lv it)).2, s.2))
  | _ => (true, ((walk lv s.1 (itOfs lv it)).2, s.2))

/-- Every item's static check. -/
def sOK (lv : ℕ → Lv) (n : ℕ) : SS → List Lvm6.Item → Bool
  | _, [] => true
  | s, it :: r => (sstep lv n s it).1 && sOK lv n (sstep lv n s it).2 r

/-- The levels agree: V1's `Lev` (height, cap and occupied words by `(ht, wd)`, openings, draws) and
CA's `Lv`; at least one opening; `1 ≤ ht ≤ 128`. -/
def levOK (sh : Lvm6.Shape) : Bool :=
  (List.range sh.levels.length).all fun i =>
    (sh.levs.getD i default).ht == (lvOf sh i).ht &&
    V.capOfL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd == (lvOf sh i).lv &&
    8 * min (V.occL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd)
      (sh.levs.getD i default).wd == (lvOf sh i).leaf &&
    (sh.levs.getD i default).t == (lvOf sh i).t && (sh.levs.getD i default).draws == (lvOf sh i).d &&
    decide (1 ≤ (lvOf sh i).t) && decide (1 ≤ (lvOf sh i).ht) && decide ((lvOf sh i).ht ≤ 128)

/-- **The static facts of the simulation** (decided per shape). -/
def simOK (sh : Lvm6.Shape) : Bool :=
  walkOK (lvOf sh) (itsOf sh) && sOK (lvOf sh) sh.levels.length (w06, none) (Lvm6.sched6 sh) && levOK sh &&
    (planOf sh).all (fun e => decide (e.len ≤ queryCap))

/-- **The static facts hold at `P18`.** -/
theorem simOK_P18 : simOK Lvm6.P18 = true := by
  unfold simOK
  rw [planOf_P18.1, Lvm6.planOf_P18_eq, Lvm6.sched6_P18_eq]
  decide +kernel

/-! ## Bytes, draws, positions -/

theorem bl_ext' (π : ByteArray) (o w : ℕ) : bl (π.extract o (o + w)) = ((bl π).drop o).take w := by
  rw [bl_extract, Nat.add_sub_cancel_left]

theorem size_of_bl {b : ByteArray} {o n : ℕ} {π : ByteArray} (h : bl b = ((bl π).drop o).take n)
    (hn : o + n ≤ π.size) : b.size = n := by
  rw [size_bl, h, List.length_take, List.length_drop, ← size_bl]; omega

theorem take_take_drop (l : List UInt8) (o m n : ℕ) :
    (l.drop o).take m ++ (l.drop (o + m)).take n = (l.drop o).take (m + n) := by
  rw [List.take_add, List.drop_drop]

theorem get!_app32 (d : Digest) (π : ByteArray) (o n m : ℕ) (hm : m < n) :
    (digestBytes d ++ π.extract o (o + n)).get! (32 + m) = π.get! (o + m) := by
  rw [get!_bl, get!_bl, bl_append, bl_digestBytes, bl_ext', List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getElem?_take, hm, List.getElem?_drop]

theorem u64At_lt (b : ByteArray) (o : ℕ) : u64At b o < 2 ^ 64 := by
  unfold u64At; exact UInt64.toNat_lt _

theorem drawN_lt (a : Digest) : drawN a < 2 ^ 128 := by
  have h1 := u64At_lt (digestBytes a) 0
  have h2 := u64At_lt (digestBytes a) 8
  unfold drawN; omega

theorem answerBits_eq' (a : Digest) : answerBits a = drawN a + 2 ^ 128 * powLane a := rfl

theorem answerBits_mod (a : Digest) : answerBits a % 2 ^ 128 = drawN a := by
  rw [answerBits_eq', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (drawN_lt a)]

/-- **V1's grind check holds where CA's does** (`g ≤ 64`). -/
theorem pw_of_powOK {g : ℕ} (hg : g ≤ 64) {a : Digest} (h : powOK g a = true) : V.pw g (answerBits a) = true := by
  simp only [powOK, decide_eq_true_eq] at h
  simp only [V.pw, decide_eq_true_eq]
  have hM : powLane a + 1 ≤ 2 ^ (64 - g) := h
  calc answerBits a = drawN a + 2 ^ 128 * powLane a := rfl
    _ < 2 ^ 128 + 2 ^ 128 * powLane a := Nat.add_lt_add_right (drawN_lt a) _
    _ = 2 ^ 128 * (powLane a + 1) := by ring
    _ ≤ 2 ^ 128 * 2 ^ (64 - g) := Nat.mul_le_mul_left _ hM
    _ = 2 ^ (192 - g) := by rw [← pow_add]; congr 1; omega

/-- The first `n` positions of a level of height `ht` whose position draws start at entry `i0`
(CA's `openPlan6` order). -/
def posAll (tr : Trace) (i0 ht n : ℕ) : List ℕ :=
  (List.range n).map fun m => posOf tr (i0 + m / (128 / ht)) (m % (128 / ht) * ht) ht

theorem posAll_snoc (tr : Trace) (i0 ht t j : ℕ) (hp : 1 ≤ 128 / ht) (hj : j * (128 / ht) < t) :
    posAll tr i0 ht (min t (j * (128 / ht))) ++
        V.posList ht (min (128 / ht) (t - j * (128 / ht))) (answerBits (aOf tr (i0 + j)) % 2 ^ 128) =
      posAll tr i0 ht (min t ((j + 1) * (128 / ht))) := by
  unfold posAll
  generalize hp' : 128 / ht = p at hp hj ⊢
  have e1 : min t (j * p) = j * p := by omega
  have e2 : min t ((j + 1) * p) = j * p + min p (t - j * p) := by rw [Nat.succ_mul]; omega
  rw [e1, e2, List.range_add, List.map_append, List.map_map]
  congr 1
  simp only [V.posList, answerBits_mod]
  apply List.map_congr_left
  intro r hr
  have hr' : r < p := by simp at hr; omega
  simp only [Function.comp, posOf]
  have hd : (j * p + r) / p = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr', Nat.zero_add]
  have hm : (j * p + r) % p = r := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
  rw [hd, hm] <;> simp [Nat.shiftRight_eq_div_pow]

theorem posAll_length (tr : Trace) (i0 ht n : ℕ) : (posAll tr i0 ht n).length = n := by simp [posAll]

/-! ## CA's accepted run, entry by entry -/

section CA

variable (c : Digest) (π : ByteArray) (F' : Trace → Bool) (tr : Trace)

/-- CA's program accepts the rest `es` of the plan from entry `i` and cursor `off`. -/
def DAcc (es : List PE6) (i off : ℕ) : Prop :=
  OProg.runSeq (tr.drop i) (drv c π F' es i off (tr.take i)) = some true

/-- The proof bytes an entry consumes. -/
def advE (e : PE6) : ℕ :=
  match e.k with
  | .q0 => 0
  | .seed => e.len - 64
  | .fs _ _ => e.len - 32
  | .leaf => e.len
  | .node .. => 32

/-- The proof bytes a list of entries consumes. -/
def consE : List PE6 → ℕ
  | [] => 0
  | e :: es => advE e + consE es

theorem consE_append (a b : List PE6) : consE (a ++ b) = consE a + consE b := by
  induction a with
  | nil => simp [consE]
  | cons e a ih => simp only [List.cons_append, consE, ih]; omega

theorem mkQ_snd (off : ℕ) (t : Trace) (i : ℕ) (e : PE6) : (mkQ c π off t i e).2 = off + advE e := by
  rcases e with ⟨k, len⟩; cases k <;> rfl

theorem runSeq_ret_false (T : Trace) : OProg.runSeq T (OProg.ret false) ≠ some true := by
  cases T <;> simp [OProg.runSeq]

variable {c π F' tr}

theorem dacc_nil {i off : ℕ} (h : DAcc c π F' tr [] i off) : tr.length ≤ i ∧ off = π.size ∧ F' tr = true := by
  unfold DAcc drv at h
  cases hT : tr.drop i with
  | cons x T => rw [hT] at h; simp [OProg.runSeq] at h
  | nil =>
    rw [hT] at h
    have hl : tr.length ≤ i := List.drop_eq_nil_iff.mp hT
    rw [List.take_of_length_le hl] at h
    simp only [OProg.runSeq, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨hl, h.1, h.2⟩

theorem dacc_cons {e : PE6} {es : List PE6} {i off : ℕ} (h : DAcc c π F' tr (e :: es) i off) :
    i < tr.length ∧ qOf tr i = (mkQ c π off (tr.take i) i e).1 ∧ postOK (tr.take (i + 1)) i e = true ∧
      DAcc c π F' tr es (i + 1) (off + advE e) := by
  unfold DAcc at h ⊢
  by_cases hi : i < tr.length
  · rw [drop_eq_cons tr hi] at h
    simp only [drv, OProg.runSeq] at h
    split at h
    · next hq =>
      rw [← hq, ← take_succ_eq tr hi] at h
      split at h
      · next hp => exact ⟨hi, hq, hp, by rwa [← mkQ_snd c π off (tr.take i) i e]⟩
      · exact absurd h (runSeq_ret_false _)
    · simp at h
  · rw [List.drop_eq_nil_of_le (by omega)] at h; simp [drv, OProg.runSeq] at h

theorem dacc_off : ∀ {es : List PE6} {i off : ℕ}, DAcc c π F' tr es i off → off + consE es = π.size
  | [], _, _, h => by simp [consE, (dacc_nil h).2.1]
  | _ :: _, _, _, h => by
    have := dacc_off (dacc_cons h).2.2.2; simp only [consE]; omega

theorem dacc_F : ∀ {es : List PE6} {i off : ℕ}, DAcc c π F' tr es i off → F' tr = true
  | [], _, _, h => (dacc_nil h).2.2
  | _ :: _, _, _, h => dacc_F (dacc_cons h).2.2.2

variable (c π F' tr)

/-- **The rest `es` of the plan, accepted from entry `i` and cursor `off`**, with its grinds and its
query lengths. -/
structure DFut (es : List PE6) (i off : ℕ) : Prop where
  acc : DAcc c π F' tr es i off
  pow : ∀ j < es.length, ∀ st g, (es.getD j default).k = .fs st g → powOK g (aOf tr (i + j)) = true
  cap : ∀ e ∈ es, e.len ≤ queryCap

variable {c π F' tr}

theorem fut_cons {e : PE6} {es : List PE6} {i off : ℕ} (h : DFut c π F' tr (e :: es) i off) :
    i < tr.length ∧ qOf tr i = (mkQ c π off (tr.take i) i e).1 ∧ postOK (tr.take (i + 1)) i e = true ∧
      (∀ st g, e.k = .fs st g → powOK g (aOf tr i) = true) ∧ e.len ≤ queryCap ∧
      off + advE e ≤ π.size ∧ DFut c π F' tr es (i + 1) (off + advE e) := by
  obtain ⟨hi, hq, hp, ha⟩ := dacc_cons h.acc
  have ho := dacc_off ha
  refine ⟨hi, hq, hp, fun st g he => ?_, h.cap e (List.mem_cons_self ..), by omega, ⟨ha, ?_, ?_⟩⟩
  · simpa using h.pow 0 (by simp) st g (by simpa using he)
  · intro j hj st g he
    have := h.pow (j + 1) (by simp; omega) st g (by simpa using he)
    rwa [show i + (j + 1) = i + 1 + j by omega] at this
  · exact fun e' he' => h.cap e' (List.mem_cons_of_mem _ he')

end CA

/-! ## CA's walk -/

theorem walk_append (lv : ℕ → Lv) : ∀ (w : WS6) (xs ys : List It),
    walk lv w (xs ++ ys) = ((walk lv w xs).1 ++ (walk lv (walk lv w xs).2 ys).1, (walk lv (walk lv w xs).2 ys).2)
  | w, [], ys => by simp [walk]
  | w, x :: xs, ys => by simp only [List.cons_append, walk]; rw [walk_append lv _ xs ys]; simp

theorem walkIt_ok (lv : ℕ → Lv) (w : WS6) (it : It) (h : (walkIt lv w it).2.ok = true) : w.ok = true := by
  cases it with
  | «open» i => simp only [walkIt] at h; split at h <;> simp_all
  | _ => simp_all [walkIt, WS6.settle]

theorem walk_ok (lv : ℕ → Lv) : ∀ (w : WS6) (its : List It), (walk lv w its).2.ok = true → w.ok = true
  | w, [], h => h
  | w, it :: r, h => walkIt_ok lv w it (walk_ok lv _ r (by simpa [walk] using h))

theorem walkIt_pend (lv : ℕ → Lv) (w : WS6) (it : It) (h : (walkIt lv w it).2.ok = true) :
    w.pend ≤ consE (walkIt lv w it).1 + (walkIt lv w it).2.pend := by
  cases it with
  | «open» i =>
    simp only [walkIt] at h ⊢; split at h
    · simp at h
    · next => simp only [Bool.and_eq_true, beq_iff_eq] at h; omega
  | D k => simp only [walkIt, Bool.and_eq_true, beq_iff_eq] at h ⊢; omega
  | _ => simp [walkIt, WS6.settle, consE, advE] <;> omega

/-- **The pending bytes are consumed by the rest of an accepted walk.** -/
theorem pend_le (lv : ℕ → Lv) : ∀ (w : WS6) (its : List It), (walk lv w its).2.ok = true →
    (walk lv w its).2.pend = 0 → w.pend ≤ consE (walk lv w its).1
  | w, [], _, hp => by simp only [walk] at hp; omega
  | w, it :: r, ho, hp => by
    simp only [walk] at ho hp ⊢
    have h1 := pend_le lv _ r ho hp
    have h2 := walkIt_pend lv w it (walk_ok lv _ r ho)
    rw [consE_append]; omega

/-! ## The relation between the two states -/

section Sim

variable (sh : Lvm6.Shape) (c : Digest) (π : ByteArray) (F' : Trace → Bool) (tr : Trace)

/-- **The relation** between CA's walk state `w` (cursor `off`, last position group `gh`) and V1's
driver state `ns`. -/
structure QRel (w : WS6) (gh : Option (ℕ × ℕ)) (off : ℕ) (ns : V.NS) : Prop where
  st : ns.st = aOf tr w.st
  stlt : w.st < w.i
  run : 1 ≤ w.run → w.st + 1 = w.i
  offE : ns.off = off + w.pend
  buf : bl ns.buf = ((bl π).drop off).take w.pend
  ncap : ns.caps.length = w.caps.length + w.pcaps.length
  caps : ∀ l ce co nb, (l, ce, co, nb) ∈ w.caps → ce < w.i ∧ ∃ o,
    ns.caps[l]? = some (o, (sh.levs.getD l default).ht, (sh.levs.getD l default).wd) ∧
      ∀ j < nb, (qOf tr ce).get! (co + j) = π.get! (o + j)
  pcaps : ∀ l po nb, (l, po, nb) ∈ w.pcaps → po + nb ≤ w.pend ∧
    ns.caps[l]? = some (off + po, (sh.levs.getD l default).ht, (sh.levs.getD l default).wd)
  ps : ∀ i0 l, gh = some (i0, l) →
    ns.ps = posAll tr i0 (sh.levs.getD l default).ht (sh.levs.getD l default).t ∧
      i0 + (sh.levs.getD l default).draws ≤ w.i

/-- **A point of the simulation**, before the items `its`. -/
structure QPt (w : WS6) (gh : Option (ℕ × ℕ)) (off : ℕ) (ns : V.NS) (its : List Lvm6.Item) : Prop where
  rel : QRel sh π tr w gh off ns
  fut : DFut c π F' tr (walk (lvOf sh) w (its.flatMap (itOfs (lvOf sh)))).1 w.i off
  ok : (walk (lvOf sh) w (its.flatMap (itOfs (lvOf sh)))).2.ok = true
  pend : (walk (lvOf sh) w (its.flatMap (itOfs (lvOf sh)))).2.pend = 0
  sok : sOK (lvOf sh) sh.levels.length (w, gh) its = true

/-- The conclusion of one item's step. -/
def StepOK (it : Lvm6.Item) (w : WS6) (gh : Option (ℕ × ℕ)) (ns : V.NS) (rest : List Lvm6.Item) : Prop :=
  let w' := (walk (lvOf sh) w (itOfs (lvOf sh) it)).2
  let s' := V.Prims.item (PA π sh.levs tr) sh.levs it (ns, w.i)
  s'.2 = w'.i ∧ ∃ off',
    (∀ k, OProg.runSeq (tr.drop w.i) (V.Prims.item (V.PN π sh.levs) sh.levs it ns k) =
      OProg.runSeq (tr.drop w'.i) (k s'.1)) ∧
    QPt sh c π F' tr w' (sstep (lvOf sh) sh.levels.length (w, gh) it).2.2 off' s'.1 rest

variable {sh c π F' tr}

theorem sstep_w (it : Lvm6.Item) (w : WS6) (gh : Option (ℕ × ℕ)) :
    (sstep (lvOf sh) sh.levels.length (w, gh) it).2.1 = (walk (lvOf sh) w (itOfs (lvOf sh) it)).2 := by
  cases it <;> rfl

/-- What a point before `it :: rest` gives for the item and for the rest. -/
theorem qpt_split {it : Lvm6.Item} {rest : List Lvm6.Item} {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ}
    {ns : V.NS} (h : QPt sh c π F' tr w gh off ns (it :: rest)) :
    DFut c π F' tr ((walk (lvOf sh) w (itOfs (lvOf sh) it)).1 ++
        (walk (lvOf sh) (walk (lvOf sh) w (itOfs (lvOf sh) it)).2 (rest.flatMap (itOfs (lvOf sh)))).1) w.i off ∧
      (walk (lvOf sh) (walk (lvOf sh) w (itOfs (lvOf sh) it)).2 (rest.flatMap (itOfs (lvOf sh)))).2.ok = true ∧
      (walk (lvOf sh) (walk (lvOf sh) w (itOfs (lvOf sh) it)).2 (rest.flatMap (itOfs (lvOf sh)))).2.pend = 0 ∧
      (walk (lvOf sh) w (itOfs (lvOf sh) it)).2.ok = true ∧ (sstep (lvOf sh) sh.levels.length (w, gh) it).1 = true ∧
      sOK (lvOf sh) sh.levels.length ((walk (lvOf sh) w (itOfs (lvOf sh) it)).2,
        (sstep (lvOf sh) sh.levels.length (w, gh) it).2.2) rest = true := by
  have hf := h.fut; have ho := h.ok; have hp := h.pend; have hs := h.sok
  simp only [List.flatMap_cons, walk_append] at hf ho hp
  simp only [sOK, Bool.and_eq_true] at hs
  refine ⟨hf, ho, hp, walk_ok _ _ _ ho, hs.1, ?_⟩
  rw [← sstep_w it w gh]; exact hs.2

theorem levOK_get (h : levOK sh = true) {i : ℕ} (hi : i < sh.levels.length) :
    (sh.levs.getD i default).ht = (lvOf sh i).ht ∧
    V.capOfL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd = (lvOf sh i).lv ∧
    8 * min (V.occL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd)
      (sh.levs.getD i default).wd = (lvOf sh i).leaf ∧
    (sh.levs.getD i default).t = (lvOf sh i).t ∧ (sh.levs.getD i default).draws = (lvOf sh i).d ∧
    1 ≤ (lvOf sh i).t ∧ 1 ≤ (lvOf sh i).ht ∧ (lvOf sh i).ht ≤ 128 := by
  simp only [levOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩ := h i hi
  exact ⟨a, b, c, d, e, f, g, k⟩

/-! ## V1's primitives against the trace -/

theorem pn_rd {w : ℕ} {ns : V.NS} (h : ns.off + w ≤ π.size) (k : V.NS → OProg Bool) :
    (V.PN π sh.levs).rd w ns k = k (aRd π w ns) := by
  simp only [V.PN, aRd]; rw [if_neg (by omega)]

theorem pn_cap {ht w : ℕ} {ns : V.NS} (h : ns.off + 32 * 2 ^ V.capOfL sh.levs ht w ≤ π.size)
    (k : V.NS → OProg Bool) : (V.PN π sh.levs).cap ht w ns k = k (aCap π sh.levs ht w ns) := by
  simp only [V.PN, aCap]; rw [if_neg (by omega)]

theorem pn_draw {chk : ℕ → Bool} {upd : List ℕ → ℕ → List ℕ} {ns : V.NS} {i : ℕ}
    (hq : 32 + ns.buf.size ≤ queryCap) (hi : i < tr.length) (hQ : qOf tr i = digestBytes ns.st ++ ns.buf)
    (hc : chk (answerBits (aOf tr i)) = true) (k : V.NS → OProg Bool) :
    OProg.runSeq (tr.drop i) ((V.PN π sh.levs).draw chk upd ns k) =
      OProg.runSeq (tr.drop (i + 1)) (k (aDraw upd (aOf tr i) ns)) := by
  simp only [V.PN, if_pos hq]
  rw [drop_eq_cons tr hi]
  simp only [OProg.runSeq]
  rw [if_pos hQ]
  simp only [hc, if_true]
  rfl

theorem pn_rep_rd (w : ℕ) : ∀ (m : ℕ) (ns : V.NS) (i : ℕ), ns.off + w * m ≤ π.size → ∀ k,
    V.Prims.rep (V.PN π sh.levs) ((V.PN π sh.levs).rd w) m ns k =
      k (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m (ns, i)).1
  | 0, ns, i, _, k => rfl
  | m + 1, ns, i, h, k => by
    have e : w * (m + 1) = w * m + w := Nat.mul_succ w m
    show (V.PN π sh.levs).rd w ns (fun ns' => V.Prims.rep (V.PN π sh.levs) ((V.PN π sh.levs).rd w) m ns' k) = _
    rw [pn_rd (by omega)]
    exact pn_rep_rd w m _ i (by simp only [aRd]; omega) k

theorem pa_rep_rd (w : ℕ) : ∀ (m : ℕ) (s : AS),
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).2 = s.2 ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).1.off = s.1.off + w * m ∧
    bl (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).1.buf =
      bl s.1.buf ++ ((bl π).drop s.1.off).take (w * m) ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).1.st = s.1.st ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).1.caps = s.1.caps ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m s).1.ps = s.1.ps
  | 0, s => by simp [V.Prims.rep, PA]
  | m + 1, s => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pa_rep_rd w m (aRd π w s.1, s.2)
    have e : V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) (m + 1) s =
      V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd w) m (aRd π w s.1, s.2) := rfl
    rw [e]
    refine ⟨h1, ?_, ?_, h4, h5, h6⟩
    · rw [h2]; show s.1.off + w + w * m = s.1.off + w * (m + 1); rw [Nat.mul_succ]; omega
    · rw [h3]
      show bl (s.1.buf ++ π.extract s.1.off (s.1.off + w)) ++ ((bl π).drop (s.1.off + w)).take (w * m) = _
      rw [bl_append, bl_ext', List.append_assoc, take_take_drop, Nat.mul_succ, Nat.add_comm (w * m) w]

/-! ## Draws -/

/-- **One draw**: the plan's chain entry `st ‖ (n pending bytes)` is V1's query; V1's checks hold. -/
theorem draw_core {chk : ℕ → Bool} {upd : List ℕ → ℕ → List ℕ} {ns : V.NS} {i st g off n : ℕ}
    {es : List PE6} (hst : ns.st = aOf tr st) (hsti : st < i) (hbuf : bl ns.buf = ((bl π).drop off).take n)
    (hF : DFut c π F' tr (⟨.fs st g, 32 + n⟩ :: es) i off)
    (hchk : powOK g (aOf tr i) = true → chk (answerBits (aOf tr i)) = true) :
    (∀ k, OProg.runSeq (tr.drop i) ((V.PN π sh.levs).draw chk upd ns k) =
      OProg.runSeq (tr.drop (i + 1)) (k (aDraw upd (aOf tr i) ns))) ∧
    DFut c π F' tr es (i + 1) (off + n) ∧ off + n ≤ π.size ∧
    qOf tr i = digestBytes (aOf tr st) ++ π.extract off (off + n) := by
  obtain ⟨hi, hq, -, hpow, hcap, hb, hF'⟩ := fut_cons hF
  simp only [advE, Nat.add_sub_cancel_left] at hb hF'
  have hq' : qOf tr i = digestBytes (aOf tr st) ++ π.extract off (off + n) := by
    rw [hq]; simp only [mkQ, aOf_take tr hsti, Nat.add_sub_cancel_left]
  refine ⟨fun k => pn_draw ?_ hi ?_ (hchk (hpow st g rfl)) k, hF', hb, hq'⟩
  · rw [size_of_bl hbuf hb]; exact hcap
  · rw [hq']; apply ba_ext
    rw [bl_append, bl_append, bl_ext', hbuf, hst]

/-- **`m` further draws** (`D m`; empty buffer, the chain from entry `st0`). -/
theorem draws_core : ∀ (m : ℕ) (ns : V.NS) (st0 i off : ℕ) (es : List PE6), st0 + 1 = i → ns.st = aOf tr st0 →
    bl ns.buf = [] →
    DFut c π F' tr (((List.range m).map fun x => (⟨.fs (st0 + x) 0, 32⟩ : PE6)) ++ es) i off →
    (∀ k, OProg.runSeq (tr.drop i) (V.Prims.rep (V.PN π sh.levs) ((V.PN π sh.levs).draw V.tt V.keepPs) m ns k) =
      OProg.runSeq (tr.drop (i + m))
        (k (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1)) ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).2 = i + m ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1.st = aOf tr (st0 + m) ∧
    bl (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1.buf = [] ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1.off = ns.off ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1.caps = ns.caps ∧
    (V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, i)).1.ps = ns.ps ∧
    DFut c π F' tr es (i + m) off
  | 0, ns, st0, i, off, es, _, hst, hb, hF => ⟨fun _ => rfl, rfl, hst, hb, rfl, rfl, rfl, by simpa using hF⟩
  | m + 1, ns, st0, i, off, es, hi, hst, hb, hF => by
    have hl : ((List.range (m + 1)).map fun x => (⟨.fs (st0 + x) 0, 32⟩ : PE6)) ++ es =
        ⟨.fs st0 0, 32 + 0⟩ :: (((List.range m).map fun x => (⟨.fs (st0 + 1 + x) 0, 32⟩ : PE6)) ++ es) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.cons_append, Nat.add_zero, List.cons.injEq, true_and]
      congr 1; apply List.map_congr_left; intro x _; simp only [Function.comp]; congr 2; omega
    rw [hl] at hF
    obtain ⟨hd, hF', -, -⟩ := draw_core (upd := V.keepPs) (chk := V.tt) hst (by omega)
      (by rw [hb, List.take_zero]) hF (fun _ => rfl)
    rw [Nat.add_zero] at hF'
    have IH := draws_core m (aDraw V.keepPs (aOf tr i) ns) (st0 + 1) (i + 1) off es (by omega)
      (by simp only [aDraw]; rw [hi]) rfl (by rwa [← hi] at hF' ⊢)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := IH
    have hP : V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) (m + 1) (ns, i) =
      V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (aDraw V.keepPs (aOf tr i) ns, i + 1) :=
      rfl
    rw [hP, show i + (m + 1) = i + 1 + m by omega, show st0 + (m + 1) = st0 + 1 + m by omega]
    refine ⟨fun k => ?_, e2, e3, e4, e5, e6, e7, e8⟩
    show OProg.runSeq (tr.drop i) ((V.PN π sh.levs).draw V.tt V.keepPs ns
      (fun ns' => V.Prims.rep (V.PN π sh.levs) ((V.PN π sh.levs).draw V.tt V.keepPs) m ns' k)) = _
    rw [hd, e1]

/-! ## Items: reads, caps, draws -/

theorem getElem?_app_some {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) (r : List α) :
    (l ++ r)[i]? = some x := by
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hi, h]

/-- **`E k`, `K k`**: `m` reads of `r` bytes, pending in CA's walk. -/
theorem step_reads {it : Lvm6.Item} (r m : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS}
    {rest : List Lvm6.Item} (h : QPt sh c π F' tr w gh off ns (it :: rest))
    (hw : walk (lvOf sh) w (itOfs (lvOf sh) it) = ([], { w with pend := w.pend + r * m }))
    (hg : (sstep (lvOf sh) sh.levels.length (w, gh) it).2.2 = gh)
    (hN : ∀ ns k, V.Prims.item (V.PN π sh.levs) sh.levs it ns k =
      V.Prims.rep (V.PN π sh.levs) ((V.PN π sh.levs).rd r) m ns k)
    (hA : ∀ s, V.Prims.item (PA π sh.levs tr) sh.levs it s =
      V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).rd r) m s) :
    StepOK sh c π F' tr it w gh ns rest := by
  obtain ⟨hf, ho, hp, -, -, hs⟩ := qpt_split h
  rw [hw] at hf ho hp hs
  rw [hg] at hs
  dsimp only at hf ho hp hs
  simp only [List.nil_append] at hf
  have R := h.rel
  have hb : w.pend + r * m ≤ _ := pend_le _ _ _ ho hp
  have hoff := dacc_off hf.acc
  obtain ⟨e2, e3, e4, e5, e6, e7⟩ := pa_rep_rd (π := π) (sh := sh) (tr := tr) r m (ns, w.i)
  dsimp only [StepOK]
  rw [hw, hg, hA]
  refine ⟨e2, off, fun k => ?_, ⟨⟨?_, R.stlt, R.run, ?_, ?_, ?_, ?_, ?_, ?_⟩, hf, ho, hp, hs⟩⟩
  · rw [hN, pn_rep_rd (π := π) (sh := sh) (tr := tr) r m ns w.i (by rw [R.offE]; omega) k]
  · rw [e5]; exact R.st
  · rw [e3]; show ns.off + r * m = off + (w.pend + r * m); rw [R.offE]; omega
  · rw [e4]; show bl ns.buf ++ _ = ((bl π).drop off).take (w.pend + r * m)
    rw [R.buf, R.offE, take_take_drop]
  · rw [e6]; exact R.ncap
  · intro l ce co nb hm; rw [e6]; exact R.caps l ce co nb hm
  · intro l po nb hm
    obtain ⟨h1, h2⟩ := R.pcaps l po nb hm
    exact ⟨by show po + nb ≤ w.pend + r * m; omega, by rw [e6]; exact h2⟩
  · intro i0 l hg'; rw [e7]; exact R.ps i0 l hg'

/-- **`cap i`**: the cap is read (V1) and pending (CA); V1's cap `i` is at the cursor. -/
theorem step_cap (hl : levOK sh = true) (i : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS}
    {rest : List Lvm6.Item} (h : QPt sh c π F' tr w gh off ns (.cap i :: rest)) :
    StepOK sh c π F' tr (.cap i) w gh ns rest := by
  obtain ⟨hf, ho, hp, -, hs1, hs⟩ := qpt_split h
  have hs1' : i = w.caps.length + w.pcaps.length ∧ i < sh.levels.length := by simpa [sstep] using hs1
  obtain ⟨-, hcl, -⟩ := levOK_get hl hs1'.2
  have hw : walk (lvOf sh) w (itOfs (lvOf sh) (.cap i)) = ([], { w with
      pcaps := (i, w.pend, 32 * 2 ^ (lvOf sh i).lv) :: w.pcaps, pend := w.pend + 32 * 2 ^ (lvOf sh i).lv }) := rfl
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) (.cap i)).2.2 = gh := rfl
  rw [hw] at hf ho hp hs
  rw [hsg] at hs
  dsimp only at hf ho hp hs
  simp only [List.nil_append] at hf
  have R := h.rel
  have hb : w.pend + 32 * 2 ^ (lvOf sh i).lv ≤ _ := pend_le _ _ _ ho hp
  have hoff := dacc_off hf.acc
  have hbound : ns.off + 32 * 2 ^ V.capOfL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd ≤
      π.size := by rw [hcl, R.offE]; omega
  dsimp only [StepOK]
  rw [hw, hsg]
  refine ⟨rfl, off, fun k => ?_, ⟨⟨R.st, R.stlt, R.run, ?_, ?_, ?_, ?_, ?_, R.ps⟩, hf, ho, hp, hs⟩⟩
  · show OProg.runSeq _ ((V.PN π sh.levs).cap _ _ ns k) = _
    rw [pn_cap hbound]; rfl
  · show ns.off + 32 * 2 ^ V.capOfL sh.levs _ _ = off + (w.pend + 32 * 2 ^ (lvOf sh i).lv)
    rw [hcl, R.offE]; omega
  · show bl (ns.buf ++ π.extract ns.off (ns.off + 32 * 2 ^ V.capOfL sh.levs _ _)) =
      ((bl π).drop off).take (w.pend + 32 * 2 ^ (lvOf sh i).lv)
    rw [hcl, bl_append, bl_ext', R.buf, R.offE, take_take_drop]
  · show (ns.caps ++ _).length = w.caps.length + (_ :: w.pcaps).length
    simp only [List.length_append, List.length_cons, List.length_nil, R.ncap]; omega
  · intro l ce co nb hm
    obtain ⟨hce, o, ho', hby⟩ := R.caps l ce co nb hm
    exact ⟨hce, o, getElem?_app_some ho' _, hby⟩
  · intro l po nb hm
    rcases List.mem_cons.mp hm with he | hm'
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨le_refl _, ?_⟩
      show (ns.caps ++ [(ns.off, _, _)])[l]? = _
      rw [hs1'.1, ← R.ncap, List.getElem?_concat_length, R.offE]
    · obtain ⟨h1, h2⟩ := R.pcaps l po nb hm'
      exact ⟨by show po + nb ≤ w.pend + 32 * 2 ^ (lvOf sh i).lv; omega, getElem?_app_some h2 _⟩

/-- The relation after a draw that settles the pending caps. -/
theorem settle_rel {w w1 : WS6} {gh gh1 : Option (ℕ × ℕ)} {off n : ℕ} {ns ns2 : V.NS}
    (R : QRel sh π tr w gh off ns) (hn : w.pend ≤ n)
    (hq : qOf tr w.i = digestBytes (aOf tr w.st) ++ π.extract off (off + n))
    (hi : w.i + 1 ≤ w1.i) (hst : w1.st < w1.i) (hrun : 1 ≤ w1.run → w1.st + 1 = w1.i) (hp : w1.pend = 0)
    (hc : w1.caps = w.pcaps.map (fun c => (c.1, w.i, 32 + c.2.1, c.2.2)) ++ w.caps) (hpc : w1.pcaps = [])
    (h1 : ns2.st = aOf tr w1.st) (h2 : bl ns2.buf = []) (h3 : ns2.off = off + n) (h4 : ns2.caps = ns.caps)
    (hps : ∀ i0 l, gh1 = some (i0, l) →
      ns2.ps = posAll tr i0 (sh.levs.getD l default).ht (sh.levs.getD l default).t ∧
        i0 + (sh.levs.getD l default).draws ≤ w1.i) :
    QRel sh π tr w1 gh1 (off + n) ns2 := by
  refine ⟨h1, hst, hrun, by rw [h3, hp, Nat.add_zero], by rw [h2, hp, List.take_zero], ?_, ?_, ?_, hps⟩
  · rw [h4, R.ncap, hc, hpc]; simp only [List.length_append, List.length_map, List.length_nil]; omega
  · intro l ce co nb hm
    rw [hc] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨⟨l', po, nb'⟩, hm', he⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at he
      obtain ⟨e1, e2, e3, e4⟩ := he
      rw [← e1, ← e2, ← e3, ← e4]
      obtain ⟨hpo, hcap⟩ := R.pcaps l' po nb' hm'
      refine ⟨by omega, off + po, by rw [h4]; exact hcap, fun j hj => ?_⟩
      rw [hq, Nat.add_assoc, get!_app32 _ _ _ _ _ (by omega), Nat.add_assoc]
    · obtain ⟨hce, o, ho, hby⟩ := R.caps l ce co nb hm
      exact ⟨by omega, o, by rw [h4]; exact ho, hby⟩
  · intro l po nb hm; rw [hpc] at hm; simp at hm

/-- **`G g`**: the nonce, then a ground draw. -/
theorem step_G (g : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS} {rest : List Lvm6.Item}
    (h : QPt sh c π F' tr w gh off ns (.G g :: rest)) : StepOK sh c π F' tr (.G g) w gh ns rest := by
  obtain ⟨hf, ho, hp, hw1, -, hs⟩ := qpt_split h
  have he : (walk (lvOf sh) w (itOfs (lvOf sh) (.G g))).1 = [⟨.fs w.st g, 32 + (w.pend + 8)⟩] := by
    simp only [itOfs, walk, walkIt, List.append_nil, List.cons.injEq, PE6.mk.injEq, and_true, true_and]; omega
  have hg : g ≤ 64 := by
    simp only [itOfs, walk, walkIt, WS6.settle, Bool.and_eq_true, decide_eq_true_eq] at hw1; omega
  rw [he, List.singleton_append] at hf
  have R := h.rel
  have hrd : ns.off + 8 ≤ π.size := by
    have := (fut_cons hf).2.2.2.2.2.1; simp only [advE] at this; rw [R.offE]; omega
  have hbuf1 : bl (aRd π 8 ns).buf = ((bl π).drop off).take (w.pend + 8) := by
    simp only [aRd]; rw [bl_append, bl_ext', R.buf, R.offE, take_take_drop]
  obtain ⟨hd, hF', -, hq⟩ := draw_core (upd := V.keepPs) (chk := V.pw g) (ns := aRd π 8 ns) R.st R.stlt hbuf1 hf
    (fun hpw => pw_of_powOK hg hpw)
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) (.G g)).2.2 = gh := rfl
  rw [hsg] at hs
  dsimp only [StepOK]
  rw [hsg]
  refine ⟨rfl, off + (w.pend + 8), fun k => ?_, ⟨?_, hF', ho, hp, hs⟩⟩
  · show OProg.runSeq _ ((V.PN π sh.levs).rd 8 ns (fun ns' => (V.PN π sh.levs).draw (V.pw g) V.keepPs ns' k)) = _
    rw [pn_rd hrd, hd]; rfl
  · refine settle_rel R (by omega) hq le_rfl (by simp [itOfs, walk, walkIt]) (fun _ => by simp [itOfs, walk, walkIt])
      (by simp [itOfs, walk, walkIt]) (by simp [itOfs, walk, walkIt, WS6.settle])
      (by simp [itOfs, walk, walkIt, WS6.settle]) rfl rfl
      (by show ns.off + 8 = _; rw [R.offE]; omega) rfl (fun i0 l hg' => ?_)
    obtain ⟨a, b⟩ := R.ps i0 l hg'
    exact ⟨a, by simp only [itOfs, walk, walkIt]; omega⟩

/-- **`B`**: a bind (one draw, no grind). -/
theorem step_B {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS} {rest : List Lvm6.Item}
    (h : QPt sh c π F' tr w gh off ns (.B :: rest)) : StepOK sh c π F' tr .B w gh ns rest := by
  obtain ⟨hf, ho, hp, -, -, hs⟩ := qpt_split h
  have he : (walk (lvOf sh) w (itOfs (lvOf sh) .B)).1 = [⟨.fs w.st 0, 32 + w.pend⟩] := rfl
  rw [he, List.singleton_append] at hf
  have R := h.rel
  obtain ⟨hd, hF', -, hq⟩ := draw_core (upd := V.keepPs) (chk := V.tt) (ns := ns) R.st R.stlt R.buf hf
    (fun _ => rfl)
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) .B).2.2 = gh := rfl
  rw [hsg] at hs
  dsimp only [StepOK]
  rw [hsg]
  refine ⟨rfl, off + w.pend, fun k => hd k, ⟨?_, hF', ho, hp, hs⟩⟩
  refine settle_rel R le_rfl hq le_rfl (by simp [itOfs, walk, walkIt]) (fun _ => by simp [itOfs, walk, walkIt])
    (by simp [itOfs, walk, walkIt]) (by simp [itOfs, walk, walkIt, WS6.settle])
    (by simp [itOfs, walk, walkIt, WS6.settle]) rfl rfl (by show ns.off = _; rw [R.offE]) rfl (fun i0 l hg' => ?_)
  obtain ⟨a, b⟩ := R.ps i0 l hg'
  exact ⟨a, by simp only [itOfs, walk, walkIt]; omega⟩

/-- **`D m`**: `m` further draws on an empty buffer. -/
theorem step_D (m : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS} {rest : List Lvm6.Item}
    (h : QPt sh c π F' tr w gh off ns (.D m :: rest)) : StepOK sh c π F' tr (.D m) w gh ns rest := by
  obtain ⟨hf, ho, hp, hw1, -, hs⟩ := qpt_split h
  have R := h.rel
  have hw1' : w.pend = 0 ∧ 1 ≤ w.run := by
    simp only [itOfs, walk, walkIt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw1
    exact ⟨hw1.1.1.2, hw1.2⟩
  have hsti := R.run hw1'.2
  have fe : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).1 =
      (List.range m).map fun x => (⟨.fs (w.st + x) 0, 32⟩ : PE6) := by
    simp only [itOfs, walk, walkIt, List.append_nil]
    apply List.map_congr_left; intro x _; split <;> simp only [PE6.mk.injEq, EK6.fs.injEq, and_true] <;> omega
  have f1 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.i = w.i + m := rfl
  have f2 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.st = w.st + m := by
    simp only [itOfs, walk, walkIt]; split <;> omega
  have f3 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.pend = w.pend := rfl
  have f4 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.caps = w.caps := rfl
  have f5 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.pcaps = w.pcaps := rfl
  have f6 : (walk (lvOf sh) w (itOfs (lvOf sh) (.D m))).2.run = w.run + m := rfl
  rw [fe] at hf
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := draws_core m ns w.st w.i off _ hsti R.st
    (by rw [R.buf, hw1'.1, List.take_zero]) hf
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) (.D m)).2.2 = gh := rfl
  rw [hsg] at hs
  dsimp only [StepOK]
  have hI : V.Prims.item (PA π sh.levs tr) sh.levs (.D m) (ns, w.i) =
      V.Prims.rep (PA π sh.levs tr) ((PA π sh.levs tr).draw V.tt V.keepPs) m (ns, w.i) := rfl
  rw [hsg, f1, hI]
  refine ⟨e2, off, fun k => e1 k, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [f1]; exact e8, ho, hp, hs⟩⟩
  · rw [e3, f2]
  · rw [f1, f2]; have := R.stlt; omega
  · intro _; rw [f1, f2]; omega
  · rw [e5, R.offE, f3]
  · rw [e4, f3, hw1'.1, List.take_zero]
  · rw [e6, R.ncap, f4, f5]
  · intro l ce co nb hm; rw [f4] at hm
    obtain ⟨hce, o, ho', hby⟩ := R.caps l ce co nb hm
    exact ⟨by rw [f1]; omega, o, by rw [e6]; exact ho', hby⟩
  · intro l po nb hm; rw [f5] at hm
    obtain ⟨h1, h2⟩ := R.pcaps l po nb hm
    exact ⟨by rw [f3]; exact h1, by rw [e6]; exact h2⟩
  · intro i0 l hg'
    obtain ⟨a, b⟩ := R.ps i0 l hg'
    exact ⟨by rw [e7]; exact a, by rw [f1]; omega⟩

/-! ## Position groups -/

/-- Positions drawn by draw `j` of a level (`p` per draw, `t` in all). -/
def cntf (p t j : ℕ) : ℕ := min p (t - j * p)

theorem lt_t_of_lt_d {t p j : ℕ} (hp : 1 ≤ p) (hj : j < (t + p - 1) / p) : j * p < t := by
  have := (Nat.le_div_iff_mul_le (by omega)).mp hj
  rw [Nat.succ_mul] at this; omega

theorem t_le_d {t p : ℕ} (hp : 1 ≤ p) : t ≤ (t + p - 1) / p * p := by
  have h1 := Nat.div_add_mod (t + p - 1) p
  have h2 := Nat.mod_lt (t + p - 1) (show 0 < p by omega)
  rw [Nat.mul_comm] at h1
  omega

/-- **The further draws of a position group** (`posRest`), from draw `j` on. -/
theorem posRest_core {ht t p d i0 : ℕ} (hp : 128 / ht = p) (hp1 : 1 ≤ p) (hd : ∀ j < d, j * p < t) :
    ∀ (m j : ℕ) (ns : V.NS) (off : ℕ) (es : List PE6), j + m = d → 1 ≤ j → ns.st = aOf tr (i0 + j - 1) →
    bl ns.buf = [] → ns.ps = posAll tr i0 ht (min t (j * p)) →
    DFut c π F' tr (((List.range m).map fun x => (⟨.fs (i0 + j - 1 + x) 0, 32⟩ : PE6)) ++ es) (i0 + j) off →
    (∀ k, OProg.runSeq (tr.drop (i0 + j))
        (V.Prims.posRest (V.PN π sh.levs) ht ((List.range' j m).map (cntf p t)) ns k) =
      OProg.runSeq (tr.drop (i0 + j + m))
        (k (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1)) ∧
    (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).2 = i0 + j + m ∧
    (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1.st =
      aOf tr (i0 + j + m - 1) ∧
    bl (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1.buf = [] ∧
    (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1.off = ns.off ∧
    (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1.caps = ns.caps ∧
    (V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j m).map (cntf p t)) (ns, i0 + j)).1.ps =
      posAll tr i0 ht (min t (d * p)) ∧
    DFut c π F' tr es (i0 + j + m) off
  | 0, j, ns, off, es, hjm, _, hst, hb, hps, hF => by
    subst hjm
    exact ⟨fun _ => rfl, rfl, hst, hb, rfl, rfl, hps, by simpa using hF⟩
  | m + 1, j, ns, off, es, hjm, hj1, hst, hb, hps, hF => by
    have hl : ((List.range (m + 1)).map fun x => (⟨.fs (i0 + j - 1 + x) 0, 32⟩ : PE6)) ++ es =
        ⟨.fs (i0 + j - 1) 0, 32 + 0⟩ ::
          (((List.range m).map fun x => (⟨.fs (i0 + (j + 1) - 1 + x) 0, 32⟩ : PE6)) ++ es) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.cons_append, Nat.add_zero, List.cons.injEq, true_and]
      congr 1; apply List.map_congr_left; intro x _
      simp only [Function.comp, PE6.mk.injEq, EK6.fs.injEq, and_true]; omega
    rw [hl] at hF
    obtain ⟨hdr, hF', -, -⟩ := draw_core (upd := V.addPs ht (cntf p t j)) (chk := V.tt) hst (by omega)
      (by rw [hb, List.take_zero]) hF (fun _ => rfl)
    rw [Nat.add_zero] at hF'
    have hps' : (aDraw (V.addPs ht (cntf p t j)) (aOf tr (i0 + j)) ns).ps = posAll tr i0 ht (min t ((j + 1) * p)) := by
      simp only [aDraw, V.addPs, hps, cntf]
      subst hp
      exact posAll_snoc tr i0 ht t j hp1 (hd j (by omega))
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := posRest_core hp hp1 hd m (j + 1)
      (aDraw (V.addPs ht (cntf p t j)) (aOf tr (i0 + j)) ns) off es (by omega) (by omega)
      (by simp only [aDraw]; congr 1) rfl hps' (by rw [show i0 + (j + 1) = i0 + j + 1 by omega]; exact hF')
    have hP : V.Prims.posRest (PA π sh.levs tr) ht ((List.range' j (m + 1)).map (cntf p t)) (ns, i0 + j) =
        V.Prims.posRest (PA π sh.levs tr) ht ((List.range' (j + 1) m).map (cntf p t))
          (aDraw (V.addPs ht (cntf p t j)) (aOf tr (i0 + j)) ns, i0 + (j + 1)) := by
      rw [List.range'_succ]; rfl
    rw [hP, show i0 + j + (m + 1) = i0 + (j + 1) + m by omega]
    refine ⟨fun k => ?_, e2, e3, e4, e5, e6, e7, e8⟩
    rw [List.range'_succ]
    show OProg.runSeq (tr.drop (i0 + j)) ((V.PN π sh.levs).draw V.tt (V.addPs ht (cntf p t j)) ns
      (fun ns' => V.Prims.posRest (V.PN π sh.levs) ht ((List.range' (j + 1) m).map (cntf p t)) ns' k)) = _
    rw [hdr]; exact e1 k

/-- **`pos i g`**: level `i`'s position group (nonce, ground draw, further draws). -/
theorem step_pos (hl : levOK sh = true) (i g : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS}
    {rest : List Lvm6.Item} (h : QPt sh c π F' tr w gh off ns (.pos i g :: rest)) :
    StepOK sh c π F' tr (.pos i g) w gh ns rest := by
  obtain ⟨hf, ho, hp, hw1, hs1, hs⟩ := qpt_split h
  have hi : i < sh.levels.length := by simpa [sstep] using hs1
  obtain ⟨hht, -, -, ht', hdr, ht1, hh1, hh128⟩ := levOK_get hl hi
  have R := h.rel
  have hg : g ≤ 64 := by
    simp only [itOfs, walk, walkIt, WS6.settle, Bool.and_eq_true, decide_eq_true_eq] at hw1; omega
  generalize hL : lvOf sh i = L at hht ht' hdr ht1 hh1 hh128
  generalize hl' : sh.levs.getD i default = l at hht ht' hdr
  have hp1L : 1 ≤ 128 / L.ht := Nat.div_pos hh128 (by omega)
  have hp1 : 1 ≤ 128 / l.ht := by rw [hht]; exact hp1L
  have hd1 : 1 ≤ l.draws := by
    rw [hdr]; show 1 ≤ (L.t + 128 / L.ht - 1) / (128 / L.ht); exact Nat.div_pos (by omega) (by omega)
  have hdt : ∀ j < l.draws, j * (128 / l.ht) < l.t := by
    rw [hdr, hht, ht']; exact fun j hj => lt_t_of_lt_d hp1L hj
  have htd : l.t ≤ l.draws * (128 / l.ht) := by rw [hdr, hht, ht']; exact t_le_d hp1L
  have fe : (walk (lvOf sh) w (itOfs (lvOf sh) (.pos i g))).1 = ⟨.fs w.st g, 32 + (w.pend + 8)⟩ ::
      (List.range (l.draws - 1)).map fun x => (⟨.fs (w.i + 1 - 1 + x) 0, 32⟩ : PE6) := by
    rw [hdr]
    simp only [itOfs, walk, walkIt, List.append_nil, List.singleton_append, WS6.settle, hL, List.cons.injEq,
      PE6.mk.injEq, and_true, true_and]
    refine ⟨by omega, ?_⟩
    apply List.map_congr_left; intro x _; split <;> simp only [PE6.mk.injEq, EK6.fs.injEq, and_true] <;> omega
  rw [fe] at hf
  have hrd : ns.off + 8 ≤ π.size := by
    have := (fut_cons hf).2.2.2.2.2.1; simp only [advE] at this; rw [R.offE]; omega
  have hbuf1 : bl (aRd π 8 { ns with ps := [] }).buf = ((bl π).drop off).take (w.pend + 8) := by
    simp only [aRd]; rw [bl_append, bl_ext', R.buf, R.offE, take_take_drop]
  have hcn : l.cnts = cntf (128 / l.ht) l.t 0 :: (List.range' 1 (l.draws - 1)).map (cntf (128 / l.ht) l.t) := by
    obtain ⟨d', hd'⟩ : ∃ d', l.draws = d' + 1 := ⟨l.draws - 1, by omega⟩
    simp only [V.Lev.cnts, V.Lev.per, hd', Nat.add_sub_cancel, List.range_eq_range', List.range'_succ,
      List.map_cons, cntf, Nat.zero_add] <;> rfl
  obtain ⟨hd, hF1, -, hq⟩ := draw_core (upd := V.addPs l.ht (cntf (128 / l.ht) l.t 0)) (chk := V.pw g)
    (ns := aRd π 8 { ns with ps := [] }) R.st R.stlt hbuf1 hf (fun hpw => pw_of_powOK hg hpw)
  have hps1 : (aDraw (V.addPs l.ht (cntf (128 / l.ht) l.t 0)) (aOf tr w.i) (aRd π 8 { ns with ps := [] })).ps =
      posAll tr w.i l.ht (min l.t (1 * (128 / l.ht))) := by
    have := posAll_snoc tr w.i l.ht l.t 0 hp1 (by omega)
    simp only [Nat.zero_mul, Nat.min_zero, Nat.add_zero, Nat.zero_add, posAll, List.range_zero, List.map_nil,
      List.nil_append] at this
    simp only [aDraw, aRd, V.addPs, List.nil_append, cntf, Nat.zero_mul, Nat.sub_zero, posAll]
    simpa using this
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := posRest_core (ht := l.ht) (t := l.t) (d := l.draws) (i0 := w.i)
    rfl hp1 hdt (l.draws - 1) 1 _ (off + (w.pend + 8)) _ (by omega) le_rfl (by simp [aDraw]) rfl hps1 hF1
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) (.pos i g)).2.2 = some (w.i, i) := rfl
  rw [hsg] at hs
  have f1 : (walk (lvOf sh) w (itOfs (lvOf sh) (.pos i g))).2.i = w.i + 1 + (l.draws - 1) := by
    rw [hdr]; simp [itOfs, walk, walkIt, WS6.settle, hL]
  have f2 : (walk (lvOf sh) w (itOfs (lvOf sh) (.pos i g))).2.st = w.i + (l.draws - 1) := by
    rw [hdr]; simp only [itOfs, walk, walkIt, WS6.settle, hL]; split <;> omega
  dsimp only [StepOK]
  rw [hsg]
  have hPA : V.Prims.item (PA π sh.levs tr) sh.levs (.pos i g) (ns, w.i) =
      V.Prims.posRest (PA π sh.levs tr) l.ht ((List.range' 1 (l.draws - 1)).map (cntf (128 / l.ht) l.t))
        (aDraw (V.addPs l.ht (cntf (128 / l.ht) l.t 0)) (aOf tr w.i) (aRd π 8 { ns with ps := [] }), w.i + 1) := by
    show V.Prims.posRest (PA π sh.levs tr) (sh.levs.getD i default).ht (sh.levs.getD i default).cnts.tail
      (aDraw (V.addPs (sh.levs.getD i default).ht ((sh.levs.getD i default).cnts.headD 0)) (aOf tr w.i)
        (aRd π 8 { ns with ps := [] }), w.i + 1) = _
    rw [hl', hcn]; rfl
  rw [hPA, f1]
  refine ⟨e2, off + (w.pend + 8), fun k => ?_, ⟨?_, by rw [f1]; exact e8, ho, hp, hs⟩⟩
  · show OProg.runSeq _ ((V.PN π sh.levs).rd 8 { ns with ps := [] } (fun ns' => (V.PN π sh.levs).draw (V.pw g)
      (V.addPs (sh.levs.getD i default).ht ((sh.levs.getD i default).cnts.headD 0)) ns'
        (fun n3 => V.Prims.posRest (V.PN π sh.levs) (sh.levs.getD i default).ht
          (sh.levs.getD i default).cnts.tail n3 k))) = _
    rw [hl', hcn, pn_rd (ns := { ns with ps := [] }) hrd]
    simp only [List.headD, List.tail]
    rw [hd, e1]
  · refine settle_rel R (by omega) hq (by rw [f1]; omega) (by rw [f1, f2]; omega) (fun _ => by rw [f1, f2]; omega)
      (by simp [itOfs, walk, walkIt, WS6.settle]) (by simp [itOfs, walk, walkIt, WS6.settle])
      (by simp [itOfs, walk, walkIt, WS6.settle]) (by rw [e3, f2]; congr 1; omega) e4
      (by rw [e5]; show ns.off + 8 = _; rw [R.offE]; omega) e6 (fun i0 l0 hg' => ?_)
    simp only [Option.some.injEq, Prod.mk.injEq] at hg'
    obtain ⟨rfl, rfl⟩ := hg'
    rw [hl', e7, Nat.min_eq_left htd, f1]
    exact ⟨rfl, by omega⟩

/-! ## Openings -/

theorem digestAt_congr {b b' : ByteArray} {o o' : ℕ} (h : ∀ j < 32, b.get! (o + j) = b'.get! (o' + j)) :
    digestAt b o = digestAt b' o' := by
  unfold digestAt; congr 1; funext x; exact h x.val x.isLt

theorem posOf_lt (tr : Trace) (pd sh0 ht : ℕ) : posOf tr pd sh0 ht < 2 ^ ht := Nat.mod_lt _ (by positivity)

theorem posOf_mod (tr : Trace) (pd sh0 ht : ℕ) : posOf tr pd sh0 ht % 2 ^ ht = posOf tr pd sh0 ht :=
  Nat.mod_eq_of_lt (posOf_lt tr pd sh0 ht)

theorem pos_shift_lt (tr : Trace) (pd sh0 : ℕ) {ht lv : ℕ} (hlv : lv ≤ ht) :
    posOf tr pd sh0 ht >>> (ht - lv) < 2 ^ lv := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hlv]
  exact posOf_lt tr pd sh0 ht

/-- A node entry of an opening's path (CA's `openPlan6`). -/
def nodeE (pd sh0 ht path ce co lvl : ℕ) : PE6 :=
  ⟨.node pd sh0 ht lvl (if lvl + 1 = path then some (ce, co, path) else none), 64⟩

/-- **A Merkle climb** of `n` levels from level `l`; the last node is the cap entry above the position. -/
theorem climb_core {ht lv ce co pd sh0 o : ℕ} (hlv : lv ≤ ht)
    (hcap : ∀ j < 32 * 2 ^ lv, (qOf tr ce).get! (co + j) = π.get! (o + j)) :
    ∀ (n l : ℕ) (d : Digest) (off i : ℕ) (es : List PE6),
    l + n = ht - lv → 1 ≤ i → pd < i → ce < i → d = aOf tr (i - 1) →
    DFut c π F' tr (((List.range n).map fun x => nodeE pd sh0 ht (ht - lv) ce co (l + x)) ++ es) i off →
    (∀ K : Digest → ℕ → OProg Bool,
      OProg.runSeq (tr.drop i) (V.climbN π n d (posOf tr pd sh0 ht % 2 ^ ht / 2 ^ l) off K) =
        OProg.runSeq (tr.drop (i + n)) (K (aOf tr (i + n - 1)) (off + 32 * n))) ∧
    DFut c π F' tr es (i + n) (off + 32 * n) ∧
    (1 ≤ n → aOf tr (i + n - 1) = digestAt π (o + 32 * (posOf tr pd sh0 ht >>> (ht - lv))))
  | 0, l, d, off, i, es, _, _, _, _, hd, hF => by
    refine ⟨fun K => ?_, by simpa using hF, fun h => absurd h (by omega)⟩
    rw [hd]; rfl
  | n + 1, l, d, off, i, es, hl, hi1, hpd, hce, hd, hF => by
    have hL : ((List.range (n + 1)).map fun x => nodeE pd sh0 ht (ht - lv) ce co (l + x)) ++ es =
        nodeE pd sh0 ht (ht - lv) ce co l ::
          (((List.range n).map fun x => nodeE pd sh0 ht (ht - lv) ce co (l + 1 + x)) ++ es) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.cons_append, Nat.add_zero, List.cons.injEq, true_and]
      congr 1; apply List.map_congr_left; intro x _; simp only [Function.comp]; congr 1; omega
    rw [hL] at hF
    obtain ⟨hi, hq, hpost, -, -, hb, hF'⟩ := fut_cons hF
    simp only [advE, nodeE] at hb hF'
    obtain ⟨IH1, IH2, IH3⟩ := climb_core hlv hcap n (l + 1) (aOf tr i) (off + 32) (i + 1) es (by omega) (by omega)
      (by omega) (by omega) (by simp) hF'
    have hq' : qOf tr i = if posOf tr pd sh0 ht % 2 ^ ht / 2 ^ l % 2 = 0 then
        digestBytes d ++ π.extract off (off + 32) else π.extract off (off + 32) ++ digestBytes d := by
      rw [hq, posOf_mod, hd]
      simp only [mkQ, nodeE, posOf_take tr hpd, aOf_take tr (show i - 1 < i by omega), Nat.shiftRight_eq_div_pow]
    refine ⟨fun K => ?_, ?_, fun _ => ?_⟩
    · simp only [V.climbN]
      rw [if_neg (by omega), drop_eq_cons tr hi]
      simp only [OProg.runSeq]
      rw [if_pos hq', Nat.div_div_eq_div_mul, ← pow_succ, IH1, show i + (n + 1) = i + 1 + n by omega,
        show off + 32 * (n + 1) = off + 32 + 32 * n by ring]
    · rw [show i + (n + 1) = i + 1 + n by omega, show off + 32 * (n + 1) = off + 32 + 32 * n by ring]; exact IH2
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp only [nodeE, if_pos (show l + 1 = ht - lv by omega), postOK, beq_iff_eq] at hpost
        rw [aOf_take tr (Nat.lt_succ_self i), qOf_take tr (by omega), posOf_take tr (by omega)] at hpost
        rw [show i + (0 + 1) - 1 = i by omega, hpost]
        apply digestAt_congr
        intro j hj
        have hx := pos_shift_lt tr pd sh0 hlv
        rw [Nat.add_assoc, Nat.add_assoc]
        exact hcap _ (by omega)
      · rw [show i + (n + 1) - 1 = i + 1 + n - 1 by omega]; exact IH3 hn

/-- **The openings at the positions `js`** (leaf, climb, cap comparison each). -/
theorem openN_core {ht lv lb pd0 ce co o : ℕ} (hlv : lv ≤ ht) (hpath : 1 ≤ ht - lv)
    (hcap : ∀ j < 32 * 2 ^ lv, (qOf tr ce).get! (co + j) = π.get! (o + j)) :
    ∀ (js : List ℕ) (off i : ℕ) (es : List PE6),
    (∀ j ∈ js, pd0 + j / (128 / ht) < i) → ce < i →
    DFut c π F' tr ((js.flatMap fun j => (⟨.leaf, lb⟩ : PE6) :: (List.range (ht - lv)).map fun lvl =>
        (⟨.node (pd0 + j / (128 / ht)) (j % (128 / ht) * ht) ht lvl
          (if lvl + 1 = ht - lv then some (ce, co, ht - lv) else none), 64⟩ : PE6)) ++ es) i off →
    (∀ K : ℕ → List ℕ → OProg Bool,
      OProg.runSeq (tr.drop i) (V.openN π o ht lv lb
          (js.map fun j => posOf tr (pd0 + j / (128 / ht)) (j % (128 / ht) * ht) ht) off K) =
        OProg.runSeq (tr.drop (i + js.length * (1 + (ht - lv))))
          (K (off + js.length * (lb + 32 * (ht - lv)))
            ((List.range js.length).map fun j => off + j * (lb + 32 * (ht - lv))))) ∧
    DFut c π F' tr es (i + js.length * (1 + (ht - lv))) (off + js.length * (lb + 32 * (ht - lv)))
  | [], off, i, es, _, _, hF => by
    refine ⟨fun K => ?_, by simpa using hF⟩
    simp only [List.map_nil, V.openN, List.length_nil, Nat.zero_mul, Nat.add_zero, List.range_zero]
  | j :: js, off, i, es, hpd, hce, hF => by
    rw [List.flatMap_cons, List.append_assoc, List.cons_append] at hF
    obtain ⟨hi, hq, -, -, -, hb, hF1⟩ := fut_cons hF
    simp only [advE] at hb hF1
    have hpdj : pd0 + j / (128 / ht) < i := hpd j (List.mem_cons_self ..)
    have hF1' : DFut c π F' tr (((List.range (ht - lv)).map fun x =>
        nodeE (pd0 + j / (128 / ht)) (j % (128 / ht) * ht) ht (ht - lv) ce co (0 + x)) ++
          ((js.flatMap fun j => (⟨.leaf, lb⟩ : PE6) :: (List.range (ht - lv)).map fun lvl =>
            (⟨.node (pd0 + j / (128 / ht)) (j % (128 / ht) * ht) ht lvl
              (if lvl + 1 = ht - lv then some (ce, co, ht - lv) else none), 64⟩ : PE6)) ++ es)) (i + 1) (off + lb) := by
      simpa only [Nat.zero_add, nodeE] using hF1
    obtain ⟨ec, hF2, htop⟩ := climb_core (π := π) (F' := F') hlv hcap (ht - lv) 0 (aOf tr i) (off + lb) (i + 1) _
      (by omega) (by omega) (by omega) (by omega) (by simp) hF1'
    have hhit : V.capHit π o ht lv (posOf tr (pd0 + j / (128 / ht)) (j % (128 / ht) * ht) ht)
        (aOf tr (i + 1 + (ht - lv) - 1)) = true := by
      rw [htop hpath]
      simp only [V.capHit, posOf_mod, ← Nat.shiftRight_eq_div_pow, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨pos_shift_lt tr _ _ hlv, trivial⟩
    obtain ⟨IH1, IH2⟩ := openN_core hlv hpath hcap js (off + lb + 32 * (ht - lv)) (i + 1 + (ht - lv)) es
      (fun j' hj' => by have := hpd j' (List.mem_cons_of_mem _ hj'); omega) (by omega)
      hF2
    have e1 : i + 1 + (ht - lv) + js.length * (1 + (ht - lv)) = i + (js.length + 1) * (1 + (ht - lv)) := by
      rw [Nat.succ_mul]; omega
    have e2 : off + lb + 32 * (ht - lv) + js.length * (lb + 32 * (ht - lv)) =
        off + (js.length + 1) * (lb + 32 * (ht - lv)) := by ring
    have e3 : off :: (List.range js.length).map (fun j => off + lb + 32 * (ht - lv) + j * (lb + 32 * (ht - lv))) =
        (List.range (js.length + 1)).map fun j => off + j * (lb + 32 * (ht - lv)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.zero_mul, Nat.add_zero, List.cons.injEq, true_and]
      apply List.map_congr_left; intro x _; simp only [Function.comp, Nat.succ_mul]; omega
    simp only [List.length_cons]
    refine ⟨fun K => ?_, by rw [← e1, ← e2]; exact IH2⟩
    simp only [List.map_cons, V.openN]
    rw [if_neg (by omega), drop_eq_cons tr hi]
    simp only [OProg.runSeq]
    rw [if_pos (by rw [hq]; rfl)]
    have ec' := ec
    simp only [pow_zero, Nat.div_one] at ec'
    rw [ec', if_pos hhit, IH1, e1, e2, e3]

/-- **`open i`**: level `i`'s openings at the last position group's positions. -/
theorem step_open (hl : levOK sh = true) (i : ℕ) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS}
    {rest : List Lvm6.Item} (h : QPt sh c π F' tr w gh off ns (.open i :: rest)) :
    StepOK sh c π F' tr (.open i) w gh ns rest := by
  obtain ⟨hf, ho, hp, hw1, hs1, hs⟩ := qpt_split h
  have R := h.rel
  have hs1' : i < sh.levels.length ∧ gh = some (w.i - 1 - (lvOf sh i).gap - ((lvOf sh i).d - 1), i) := by
    simpa [sstep] using hs1
  obtain ⟨hht, hcl, hlb, ht', hdr, ht1, hh1, hh128⟩ := levOK_get hl hs1'.1
  have hsg : (sstep (lvOf sh) sh.levels.length (w, gh) (.open i)).2.2 = gh := rfl
  rw [hsg] at hs
  cases hfd : w.caps.find? (·.1 == i) with
  | none => simp [itOfs, walk, walkIt, hfd] at hw1
  | some r =>
    obtain ⟨l', ce, co, nb⟩ := r
    have hmem : (l', ce, co, nb) ∈ w.caps := List.mem_of_find?_eq_some hfd
    have hl' : l' = i := by simpa using List.find?_some hfd
    rw [hl'] at hmem
    have hok : w.pend = 0 ∧ w.pcaps = [] ∧ 1 ≤ (lvOf sh i).ht - (lvOf sh i).lv ∧
        (lvOf sh i).lv ≤ (lvOf sh i).ht ∧ nb = 32 * 2 ^ (lvOf sh i).lv := by
      simp only [itOfs, walk, walkIt, hfd, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.isEmpty_iff] at hw1
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, a⟩, b⟩, -⟩, -⟩, d'⟩, e⟩, -⟩, -⟩, f⟩ := hw1
      exact ⟨a, b, d', e, f⟩
    obtain ⟨hpend, hpc, hpath, hlv, hnb⟩ := hok
    have fe : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).1 =
        openPlan6 (lvOf sh i) (w.i - 1 - (lvOf sh i).gap - ((lvOf sh i).d - 1)) ce co := by
      simp [itOfs, walk, walkIt, hfd]
    have f1 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.i =
        w.i + (lvOf sh i).t * (1 + ((lvOf sh i).ht - (lvOf sh i).lv)) := by simp [itOfs, walk, walkIt, hfd, Lv.path]
    have f2 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.st = w.st := by simp [itOfs, walk, walkIt, hfd]
    have f3 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.pend = w.pend := by simp [itOfs, walk, walkIt, hfd]
    have f4 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.caps = w.caps := by simp [itOfs, walk, walkIt, hfd]
    have f5 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.pcaps = w.pcaps := by
      simp [itOfs, walk, walkIt, hfd]
    have f6 : (walk (lvOf sh) w (itOfs (lvOf sh) (.open i))).2.run = 0 := by simp [itOfs, walk, walkIt, hfd]
    rw [fe] at hf
    obtain ⟨hpsR, hpdR⟩ := R.ps _ i hs1'.2
    obtain ⟨hce, o, hco, hby⟩ := R.caps i ce co nb hmem
    have hoff0 : ns.off = off := by rw [R.offE, hpend, Nat.add_zero]
    have hp1 : 1 ≤ 128 / (lvOf sh i).ht := Nat.div_pos hh128 (by omega)
    have hOC := openN_core (π := π) (F' := F') (ht := (lvOf sh i).ht) (lv := (lvOf sh i).lv) (lb := (lvOf sh i).leaf)
      (pd0 := w.i - 1 - (lvOf sh i).gap - ((lvOf sh i).d - 1)) (o := o) hlv hpath
      (fun j hj => hby j (by rw [hnb]; exact hj)) (List.range (lvOf sh i).t) off w.i _
      (fun j hj => by
        have hj' := List.mem_range.mp hj
        have htd : (lvOf sh i).t ≤ (lvOf sh i).d * (128 / (lvOf sh i).ht) := t_le_d hp1
        have : j / (128 / (lvOf sh i).ht) < (lvOf sh i).d := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        rw [hdr] at hpdR; omega) hce hf
    simp only [List.length_range] at hOC
    obtain ⟨hk, hF2⟩ := hOC
    have hlen : ns.ps.length = (lvOf sh i).t := by rw [hpsR, posAll_length, ht']
    dsimp only [StepOK]
    rw [hsg]
    have hPA : V.Prims.item (PA π sh.levs tr) sh.levs (.open i) (ns, w.i) =
        (aOpn sh.levs i (sh.levs.getD i default).ht (sh.levs.getD i default).wd ns,
          w.i + ns.ps.length * (1 + ((sh.levs.getD i default).ht -
            V.capOfL sh.levs (sh.levs.getD i default).ht (sh.levs.getD i default).wd))) := by
      simp only [V.Prims.item, PA, hco]
    rw [hPA, f1]
    refine ⟨by rw [hlen, hcl, hht], off + (lvOf sh i).t * ((lvOf sh i).leaf + 32 * ((lvOf sh i).ht - (lvOf sh i).lv)),
      fun k => ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [f1]; exact hF2, ho, hp, hs⟩⟩
    · show OProg.runSeq _ ((V.PN π sh.levs).opn i ns k) = _
      have hlen' : ns.ps.length = (sh.levs.getD i default).t := by rw [hpsR, posAll_length]
      rw [← hht, ← hcl, ← hlb, ← ht'] at hk
      simp only [V.PN, hco]
      rw [hpsR, hoff0]
      unfold posAll
      rw [hk]
      simp only [aOpn, opnB]
      rw [hlen', hpsR, hoff0]
      unfold posAll
      rw [← ht', ← hht, ← hcl]
    · rw [f2]; exact R.st
    · rw [f1, f2]; have := R.stlt; omega
    · intro h; rw [f6] at h; omega
    · show ns.off + ns.ps.length * opnB sh.levs _ _ = _
      rw [f3, hpend, hlen, hoff0, Nat.add_zero]
      simp only [opnB]
      rw [hcl, hlb, hht]
    · rw [f3, hpend, List.take_zero]; show bl ns.buf = []; rw [R.buf, hpend, List.take_zero]
    · rw [f4, f5]; exact R.ncap
    · intro l ce' co' nb' hm; rw [f4] at hm
      obtain ⟨hce', o', ho', hby'⟩ := R.caps l ce' co' nb' hm
      exact ⟨by rw [f1]; omega, o', ho', hby'⟩
    · intro l po nb' hm; rw [f5, hpc] at hm; simp at hm
    · intro i0 l hg'
      obtain ⟨a, b⟩ := R.ps i0 l hg'
      exact ⟨a, by rw [f1]; omega⟩

/-! ## The schedule -/

theorem step (hl : levOK sh = true) (it : Lvm6.Item) {w : WS6} {gh : Option (ℕ × ℕ)} {off : ℕ} {ns : V.NS}
    {rest : List Lvm6.Item} (h : QPt sh c π F' tr w gh off ns (it :: rest)) :
    StepOK sh c π F' tr it w gh ns rest := by
  cases it with
  | E k => exact step_reads 16 k h rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  | K k => exact step_reads 8 k h rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  | cap i => exact step_cap hl i h
  | G g => exact step_G g h
  | D k => exact step_D k h
  | B => exact step_B h
  | pos i g => exact step_pos hl i g h
  | «open» i => exact step_open hl i h

/-- **The simulation over the schedule.** -/
theorem sim_walk (hl : levOK sh = true) : ∀ (its : List Lvm6.Item) (w : WS6) (gh : Option (ℕ × ℕ)) (off : ℕ)
    (ns : V.NS), QPt sh c π F' tr w gh off ns its →
    ∃ w' gh' off', (∀ k, OProg.runSeq (tr.drop w.i) (V.Prims.walk (V.PN π sh.levs) sh.levs its ns k) =
      OProg.runSeq (tr.drop w'.i) (k (V.Prims.walk (PA π sh.levs tr) sh.levs its (ns, w.i)).1)) ∧
      (V.Prims.walk (PA π sh.levs tr) sh.levs its (ns, w.i)).2 = w'.i ∧
      QPt sh c π F' tr w' gh' off' (V.Prims.walk (PA π sh.levs tr) sh.levs its (ns, w.i)).1 []
  | [], w, gh, off, ns, h => ⟨w, gh, off, fun _ => rfl, rfl, h⟩
  | it :: rest, w, gh, off, ns, h => by
    obtain ⟨h2, off1, heq, hpt⟩ := step hl it h
    obtain ⟨w', gh', off', heq', h2', hpt'⟩ := sim_walk hl rest _ _ off1 _ hpt
    have hs : ((V.Prims.item (PA π sh.levs tr) sh.levs it (ns, w.i)).1,
        (walk (lvOf sh) w (itOfs (lvOf sh) it)).2.i) = V.Prims.item (PA π sh.levs tr) sh.levs it (ns, w.i) := by
      rw [← h2]
    rw [hs] at heq' h2' hpt'
    refine ⟨w', gh', off', fun k => (heq _).trans (heq' k), h2', hpt'⟩

end Sim

/-! ## CA's driver accepts ⇒ `VS6` accepts -/

/-- **CA2's link**: if `drive6 (planOf sh) c π F'` accepts the trace and `F'` gives the header check, the
grinds and `F π (accOf sh π tr)`, then V1's `VS6` accepts the trace. -/
theorem vs6_of_drive6 (sh : Lvm6.Shape) (hS : simOK sh = true) {F' : Trace → Bool}
    {F : ByteArray → List V.NV → Bool} {vk c : Digest} {π : ByteArray} {tr : Trace}
    (hD : OProg.runSeq tr (drive6 (planOf sh) c π F') = some true)
    (hF : F' tr = true → V.hdrOkWith leafStmtF nodeStmtF (2 ^ sh.logN) vk c (π.extract 0 (Lvm6.hdrLen sh)) = true ∧
      PowOK6 (planOf sh) tr ∧ F π (accOf sh π tr) = true) :
    OProg.runSeq tr (V.VS6 (Lvm6.toV sh) F vk c π) = some true := by
  simp only [simOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨hW, hsok⟩, hl⟩, hcap⟩ := hS
  have hA : DAcc c π F' tr (planOf sh) 0 0 := by simpa [DAcc, drive6] using hD
  obtain ⟨hH, hP, hFa⟩ := hF (dacc_F hA)
  have hFut : DFut c π F' tr (planOf sh) 0 0 := ⟨hA, fun j hj st g he => by simpa using hP j hj st g he, hcap⟩
  unfold planOf at hFut
  obtain ⟨h0, hq0, -, -, -, -, hF1⟩ := fut_cons hFut
  obtain ⟨h1, hq1, -, -, hc1, hb1, hF2⟩ := fut_cons hF1
  simp only [advE, Lvm6.seedLen, Nat.add_sub_cancel_left, Nat.zero_add] at hc1 hb1 hF2 hq1
  simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at hW
  obtain ⟨⟨hok, hpend⟩, -⟩ := hW
  have hpt : QPt sh c π F' tr w06 none (Lvm6.hdrLen sh) (ns0 sh (aOf tr 1)) (Lvm6.sched6 sh) :=
    ⟨⟨rfl, by decide, fun h => absurd h (by decide), rfl, rfl, rfl, fun _ _ _ _ h => by simp [w06] at h,
      fun _ _ _ h => by simp [w06] at h, fun _ _ h => by simp at h⟩, hF2, hok, hpend, hsok⟩
  obtain ⟨w', gh', off', heq, -, hpt'⟩ := sim_walk hl _ _ _ _ _ hpt
  have hfut' := hpt'.fut
  simp only [List.flatMap_nil, walk] at hfut'
  obtain ⟨hlen, hoff, -⟩ := dacc_nil hfut'.acc
  have hp' := hpt'.pend
  simp only [List.flatMap_nil, walk] at hp'
  have hoffV := hpt'.rel.offE
  unfold V.VS6
  rw [if_pos (show V.hdrLen (Lvm6.toV sh) ≤ π.size by simpa [V.hdrLen, Lvm6.hdrLen, Lvm6.toV] using hb1)]
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hH, hc1⟩)]
  have htr : tr = tr.drop 0 := rfl
  rw [htr, drop_eq_cons tr h0]
  simp only [OProg.runSeq]
  rw [if_pos (by rw [hq0]; rfl), drop_eq_cons tr h1]
  simp only [OProg.runSeq]
  rw [if_pos (by rw [hq1]; simp [mkQ, aOf_take tr (show 0 < 1 by omega), V.hdrLen, Lvm6.hdrLen, Lvm6.toV])]
  refine (heq (fun ns => OProg.ret (F π ns.acc && decide (π.size ≤ ns.off)))).trans ?_
  rw [List.drop_eq_nil_of_le hlen]
  simp only [OProg.runSeq, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hFa, by rw [hoffV, hp', hoff]; omega⟩

end Lvm6.Q
