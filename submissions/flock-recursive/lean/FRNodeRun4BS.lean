-- G6: this module also holds the former modules `FRNodeRun4BR` (one section each, in import order).
import FRNodeRun4BL
import FRNodeRows4AskIR

section G6_FRNodeRun4BR

-- New for `flock-recursive` (IMPC2 §7 step 3 item 2; track IMPC2b): the bits' run proofs — `bitOf`'s imports,
-- `bits n`'s auxiliary cells and the statement's two flags (tag, zero tail) on the answer-driven run; `SlotRunB`.

/-!
# `SlotRunA` with the bits

`SlotRunA` (B3) states three run facts on the answer-driven run. `bitTGB`'s rows (`FRNodeRows4AskB`) and
the bit sources' values (`FRNodeRun4BL.SrcOk`) discharge three classes of them:

* **a `bitOf r h` import followed by a `selectHalf` on it** (`bitNx`): the following op's rows make
  its cell the bit's source, which holds bit `h` of register `r` (`impA_bits`, an induction along the
  compile's trail and the run together); the residual imports are `impBX` (`impAX` less those);
* **a `bits n` auxiliary import** (only a `tensorW` carries one, `xof_bits`): `auxBRows` make its cells
  the register's bits (`aux_bits`);
* **the statement's tag byte and zero tail** (`stFlag`): `StmtBits` gives them (`flag_stmt`).

**`SlotRunB`** is the residual (IMPC's zero pins also discharged), **`slotRunA_of_bits`** the
reduction.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

theorem outs_eq_nOut (op : Op) : op.outs = op.nOut := by cases op <;> rfl

/-! ## Slots along the compile -/

theorem add_slots_size (c : CS) (op : Op) (o : Out) : (c.add op o).slots.size = c.slots.size + o.slots.length := by
  simp [CS.add]

theorem compileFromX_slot_lt (X : Ext) (P : Params) : ∀ (ops : List Op) (cs : CS) {i : ℕ},
    i < cs.slots.size → (compileFromX X P cs ops).slot i = cs.slot i
  | [], _, _, _ => rfl
  | op :: ops, cs, i, hi => by
    rw [compileFromX_cons, compileFromX_slot_lt X P ops _ (by rw [add_slots_size, CS.align_slots]; omega),
      slot_add_old (by rw [CS.align_slots]; exact hi), CS.align_slot]

/-! ## `bitOf`'s imports -/

/-- **A `bitOf` followed by a `selectHalf` on its result** (register `n`). -/
def bitNx : Op → List Op → ℕ → Bool
  | .bitOf _ _, .selectHalf b _ _ :: _, n => decide (b = n)
  | _, _, _ => false

/-- **The residual imports less the bits'**: `impAX` without the `bitOf` imports `bitNx` marks. -/
def impBX (X : Ext) (P : Params) (rt : RT) (A : AT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op && !A.cov op && !op.item?.isSome && !bitNx op ops c.slots.size then
        List.range' c.slots.size (stepOut X P c op).slots.length else []) ++
      impBX X P rt A (c.add op (stepOut X P c op)) ops

section Bits
variable {impl : OpImpl} {ι : Kind} {inp : Input} {w : Asg} {P : Params} {X Xa : Ext} {rt : RT} {A : AT}
  {T : BTab} {π : ℕ} {s' : St} {tr' : Trace}

/-- **The bits' imports on the run**: along the trail and the answer-driven run together, a residual
import that `impBX` drops (a `bitOf r h` whose next op is a `selectHalf` on it) holds its value, the
next op's rows (`bitRowsB`) making its cell the bit's source. -/
theorem impA_bits (hP : SelOk w P ι) (hlen : ∀ c op, (stepOut X P c op).slots.length = op.nOut)
    (hcov : ∀ b x y, A.cov (.selectHalf b x y) = true)
    (hrA : ∀ c pre op k, ∀ r ∈ bitRowsB T Xa π P c pre op k, r ∈ A.rows P c pre op k)
    (hsrc : SrcOk T w π ι s'.regs) :
    ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ) (s : St) (tr0 : Trace),
    execA impl ι inp ops s tr0 = some (s', tr') → cs.slots.size = s.regs.size →
    (∀ r ∈ askRowsX X P A cs pre k ops, r.Holds w) →
    ∀ i ∈ impAX X P rt A cs ops, i ∉ impBX X P rt A cs ops →
      RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)
  | [], _, _, _, _, _, _, _, _, i, hi, _ => by simp [impAX] at hi
  | op :: ops, cs, pre, k, s, tr0, he, hsz, hra, i, hi, hb => by
    rw [impAX_cons, List.mem_append] at hi
    simp only [impBX, List.mem_append, not_or] at hb
    rw [askRowsX_cons] at hra
    rw [compileFromX_cons]
    generalize hc : cs.align (alignOf op ops) = c at hi hb hra
    have hcs : c.slots.size = s.regs.size := by rw [← hc, CS.align_slots, hsz]
    -- the run's step
    simp only [execA] at he
    split at he
    · next vs ok hv =>
      have hsz' : (c.add op (stepOut X P c op)).slots.size = (s.regs ++ vs.toArray).size := by
        have hl := Circ.evalOp_len hv
        simp [add_slots_size, hlen, hcs, hl]
      rcases hi with hi | hi
      · -- the head: a `bitOf` with its next op
        split_ifs at hi with hA
        swap; · cases hi
        have hB : bitNx op ops c.slots.size = true := by
          by_contra hn
          exact hb.1 (by rw [if_pos (by simp_all)]; exact hi)
        obtain ⟨hmem, hlt⟩ := List.mem_range'_1.1 hi
        obtain ⟨r, h, x, y, ops', rfl, rfl⟩ : ∃ r h x y ops', op = .bitOf r h ∧
            ops = .selectHalf c.slots.size x y :: ops' := by
          cases op <;> simp [bitNx] at hB
          rcases ops with _ | ⟨op2, ops'⟩
          · simp [bitNx] at hB
          cases op2 <;> simp [bitNx] at hB
          subst hB
          exact ⟨_, _, _, _, _, rfl, rfl⟩
        rename' ops' => ops
        have hl1 : (stepOut X P c (.bitOf r h)).slots.length = 1 := by rw [hlen]; rfl
        have hi' : i = c.slots.size := by omega
        subst hi'
        -- the next op's rows
        rw [askRowsX_cons] at hra
        set c1 := c.add (.bitOf r h) (stepOut X P c (.bitOf r h)) with hc1
        set c2 := c1.align (alignOf (.selectHalf c.slots.size x y) ops) with hc2
        have hrows : ∀ r0 ∈ bitRowsB T Xa π P c2 (some (.bitOf r h)) (.selectHalf c.slots.size x y) k, r0.Holds w :=
          fun r0 hr0 => hra r0 (List.mem_append_right _ (List.mem_append_left _ (by
            rw [if_pos (by simp [hcov])]; exact hrA _ _ _ _ r0 hr0)))
        unfold bitRowsB at hrows
        dsimp only at hrows
        split at hrows
        · exact absurd (hrows _ List.mem_cons_self) (failRT_not hP.1)
        split at hrows
        · rename_i l hsl
          split_ifs at hrows with hg
          · obtain ⟨xs, hxs, hev⟩ := selRows_ev hP hrows
            have hs := hsrc r h xs hxs
            -- the final slot
            have hfin : (compileFromX X P c1 (.selectHalf c.slots.size x y :: ops)).slot c.slots.size =
                some (.bit, [l]) := by
              rw [compileFromX_slot_lt X P _ _ (by rw [hc1, add_slots_size, hl1]; omega), ← hsl, hc2, CS.align_slot]
            rw [hfin]
            -- the run's value
            have hv' := hv
            simp only [evalOp, Res.vals.injEq] at hv'
            obtain ⟨rfl, -⟩ := hv'
            obtain ⟨more, hm⟩ := execA_prefix _ _ _ he
            have hval : rd s'.regs c.slots.size = .bit ((rd s.regs r).toN.testBit h) := by
              rw [hm, rd, Array.getElem?_append_left (by simp [hcs]), hcs]; simp
            have hrr : rd s.regs r = rd s'.regs r := by
              rw [hm, Array.append_assoc, rd_prefix (by rw [← hcs]; exact hg.2)]
            rw [hval, hrr]
            refine ⟨rfl, ?_⟩
            simp only [List.map_cons, List.map_nil, encV, hev, srcVal_of_srcV hs]
          · exact absurd (hrows _ List.mem_cons_self) (failRT_not hP.1)
        · exact absurd (hrows _ List.mem_cons_self) (failRT_not hP.1)
      · exact impA_bits hP hlen hcov hrA hsrc ops _ (some op) _ _ tr0 he hsz'
          (fun r0 hr0 => hra r0 (List.mem_append_right _ hr0)) i hi hb.2
    · next q hq =>
      rcases tr0 with _ | ⟨⟨q', a⟩, tr1⟩
      · cases he
      have hsz' : (c.add op (stepOut X P c op)).slots.size = (s.regs.push (.d a)).size := by
        rw [add_slots_size, hlen, Array.size_push, hcs, ask_nOut hq]
      rcases hi with hi | hi
      · split_ifs at hi with hA
        · simp [ask_item hq] at hA
        · cases hi
      · exact impA_bits hP hlen hcov hrA hsrc ops _ (some op) _ _ tr1 he hsz'
          (fun r0 hr0 => hra r0 (List.mem_append_right _ hr0)) i hi hb.2

end Bits

/-! ## `bits n`'s auxiliary imports -/

theorem opOut_aux' (P : Params) (cs : CS) (op : Op) : (opOut P cs op).aux = [] := opOut_aux P cs op

theorem tplExt_bits {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out} (h : tplExt tc P cs op = some o)
    {a : List Lin × ℕ × AuxK} (ha : a ∈ o.aux) {n : ℕ} (hn : a.2.2 = .bits n) : isTensorW op = true := by
  cases op
  case tensorW => rfl
  all_goals (simp only [tplExt] at h; repeat' (first | (split at h) | (split_ifs at h)))
  all_goals (cases h <;> first | (simp [tplOut] at ha; done) | (simp at ha; subst ha; simp at hn))

theorem tplExtKM_bits {F : TFilt} {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out}
    (h : tplExtKM F tc P cs op = some o) {a : List Lin × ℕ × AuxK} (ha : a ∈ o.aux) {n : ℕ}
    (hn : a.2.2 = .bits n) : isTensorW op = true := by
  cases op
  case tensorW => rfl
  all_goals (simp only [tplExtKM] at h; repeat' (first | (split at h) | (split_ifs at h)))
  all_goals (cases h <;> first | (simp [tplOut] at ha; done) | (simp at ha; subst ha; simp at hn))

/-- **Only a `tensorW` carries a `bits` auxiliary import** (prototype `π`'s compile). -/
theorem xof_bits {π : ℕ} {P : Params} {cs : CS} {op : Op} {a : List Lin × ℕ × AuxK}
    (ha : a ∈ (stepOut (Xof π) P cs op).aux) {n : ℕ} (hn : a.2.2 = .bits n) : isTensorW op = true := by
  by_cases hd : ∃ w col, op = .dotKF w col
  · obtain ⟨w, col, rfl⟩ := hd
    exfalso
    simp only [stepOut] at ha
    cases hx : Xof π P cs (.dotKF w col) with
    | none => rw [hx, Option.getD_none, opOut_aux] at ha; cases ha
    | some o =>
      rw [hx, Option.getD_some] at ha
      rw [xof_dk] at hx
      obtain ⟨_, _, -, -, hau, -⟩ := dkA_some hx
      rw [hau, List.mem_singleton] at ha; subst ha; cases hn
  simp only [stepOut, xof_ne fun w col he => hd ⟨w, col, he⟩] at ha
  cases hx : tplExt4 (protoF π) (protoR π) (protoLay π).ctx P cs op with
  | none => rw [hx, Option.getD_none, opOut_aux] at ha; cases ha
  | some o =>
    rw [hx, Option.getD_some] at ha
    simp only [tplExt4, Ext.orElse] at hx
    cases h4 : tplExt4S (protoF π) (protoR π) (protoLay π).ctx P cs op with
    | some o' =>
      rw [h4, Option.orElse_some, Option.some.injEq] at hx
      subst hx
      unfold tplExt4S at h4
      split at h4
      · split at h4 <;> [split_ifs at h4; cases h4] <;> cases h4 <;> simp [tplOut] at ha
      · split at h4 <;> [split_ifs at h4; cases h4] <;> cases h4 <;> simp [tplOut] at ha
      · obtain ⟨h5, -⟩ := Option.filter_eq_some_iff.1 h4
        exact tplExt_bits h5 ha hn
    | none =>
      rw [h4, Option.orElse_none] at hx
      split_ifs at hx
      cases h6 : tplExtKM (protoF π) (protoLay π).ctx P cs op with
      | some o' =>
        rw [h6, Option.orElse_some, Option.some.injEq] at hx
        subst hx; exact tplExtKM_bits h6 ha hn
      | none =>
        rw [h6, Option.orElse_none] at hx
        rw [extGetK_aux hx] at ha; cases ha

theorem auxBRows_mem {T : BTab} {P : Params} {π m : ℕ} {cells : List Lin} {r n : ℕ}
    {l : List (List Lin × ℕ × AuxK)} (h : (cells, r, AuxK.bits n) ∈ l) :
    ∀ x ∈ (if r < m ∧ cells.length = n then cells.zipIdx.flatMap fun p => selRows P π p.1 (T.bitSrc r p.2)
      else [failRT P]), x ∈ auxBRows T P π m l := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    intro x hx
    obtain ⟨y1, y2, y3⟩ := y
    rcases List.mem_cons.1 h with e | hl
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      simp only [auxBRows]; exact List.mem_append_left _ hx
    · have := ih hl x hx
      cases y3 <;> simp only [auxBRows]
      · exact this
      · exact List.mem_append_right _ this

/-- **A `bits n` auxiliary import holds** where `auxBRows`' rows hold and the sources hold the bits. -/
theorem aux_bits {P : Params} {w : Asg} {ι : Kind} {T : BTab} {π : ℕ} {regs : Array Val} (hP : SelOk w P ι)
    (hsrc : SrcOk T w π ι regs) {cells : List Lin} {r n m : ℕ}
    (hrows : ∀ x ∈ (if r < m ∧ cells.length = n then cells.zipIdx.flatMap fun p => selRows P π p.1 (T.bitSrc r p.2)
        else [failRT P]), x.Holds w) :
    cells.map (Lin.ev w) = (AuxK.bits n).val (rd (regs.extract 0 m) r) := by
  split_ifs at hrows with hg
  · rw [rd_extract hg.1]
    refine List.ext_getElem (by simp [AuxK.val, hg.2]) fun b h1 h2 => ?_
    simp only [List.length_map] at h1
    simp only [List.getElem_map, AuxK.val, List.getElem_range]
    have hmem : (cells[b], b) ∈ cells.zipIdx := by
      rw [List.mem_iff_getElem?]; exact ⟨b, by simp [List.getElem?_zipIdx, h1]⟩
    obtain ⟨x, hx, hev⟩ := selRows_ev hP fun row hr => hrows row (List.mem_flatMap.2 ⟨_, hmem, hr⟩)
    rw [hev, srcVal_of_srcV (hsrc r b x hx)]
    rfl
  · exact absurd (hrows _ List.mem_cons_self) (failRT_not hP.1)

/-! ## The statement's flags -/

/-- **The statement's two flags**: its tag byte (`assertEq` of the 1-byte read at `so` and the tag
constant) and its zero tail (`assertZero` of the read `[so + z, so + L)`), as `T` describes them. -/
def stFlag (T : BTab) (p : Op × ℕ) : Bool :=
  match T.st, p.1 with
  | some s, .assertEq a b _ =>
    match T.rt.getD a .none, T.rt.getD b .none with
    | .pf o 1, .cb bs => decide (o = s.so ∧ bs.data = #[s.t] ∧ s.t ≠ 0 ∧ a < p.2 ∧ b < p.2)
    | _, _ => false
  | some s, .assertZero a _ =>
    match T.rt.getD a .none with
    | .pf o len => decide (o = s.so + s.z ∧ o + len = s.so + s.L ∧ a < p.2)
    | _ => false
  | _, _ => false

theorem byte_eq_zero {x : UInt8} (h : ∀ t < 8, x.toNat.testBit t = false) : x = 0 := by
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq; intro t
  by_cases ht : t < 8
  · rw [h t ht]; simp
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

/-- **The statement's flags hold** on registers whose provenance `riAcc` describes, given `StmtBits`. -/
theorem flag_stmt {impl : OpImpl} {ι : Kind} {inp : Input} {tr : Trace} {w : Asg} {π : ℕ} {T : BTab}
    {regs : Array Val} (hri : ∀ r, RIV ι inp tr regs (T.rt.getD r .none) (rd regs r))
    (hS : StmtBits T w π inp.π) {p : Op × ℕ} (hp : stFlag T p = true) :
    flagOf impl ι inp (regs.extract 0 p.2) p.1 = true := by
  obtain ⟨op, m⟩ := p
  unfold stFlag at hp
  split at hp
  · rename_i s a b act hs hop
    simp only at hop; subst hop
    split at hp
    · rename_i o bs ha hb
      simp only [decide_eq_true_eq] at hp
      obtain ⟨rfl, hbs, ht0, ham, hbm⟩ := hp
      have hra := hri a; rw [ha] at hra
      have hrb := hri b; rw [hb] at hrb
      simp only [flagOf, evalOp, rd_extract ham, rd_extract hbm]
      rw [show rd regs a = _ from hra, show rd regs b = _ from hrb]
      simp only [Val.eqv, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      right
      have htag := hS.1 s hs
      have hlt : s.so < inp.π.size := by
        by_contra hn; unfold byteAt at htag; rw [dif_neg hn] at htag; exact ht0 htag.symm
      rw [hbs]
      apply Array.ext (by simp [ByteArray.data_extract]; omega)
      intro j h1 h2
      have hj : j = 0 := by simp at h2; omega
      subst hj
      simp only [ByteArray.data_extract, Array.getElem_extract, Nat.add_zero, List.getElem_toArray,
        List.getElem_cons_zero]
      unfold byteAt at htag; rw [dif_pos hlt] at htag; exact htag
    · cases hp
  · rename_i s a act hs hop
    simp only at hop; subst hop
    split at hp
    · rename_i o len ha
      simp only [decide_eq_true_eq] at hp
      obtain ⟨rfl, hL, ham⟩ := hp
      have hra := hri a; rw [ha] at hra
      simp only [flagOf, evalOp, rd_extract ham]
      rw [show rd regs a = _ from hra]
      simp only [Val.isZero, Bool.or_eq_true, Bool.not_eq_true']
      right
      rw [Array.all_eq_true]
      intro i hi
      have hi' : i < min (s.so + s.z + len) inp.π.data.size - (s.so + s.z) := by
        simpa [ByteArray.data_extract, Array.size_extract] using hi
      simp only [ByteArray.data_extract, Array.getElem_extract, beq_iff_eq]
      have hil : i < len := by have := hi'; omega
      have hz : ∀ t < 8, (byteAt inp.π (s.so + s.z + i)).toNat.testBit t = false := by
        intro t ht
        have hc : T.stCell (8 * (s.z + i) + t) = some none := by
          simp only [BTab.stCell, hs]
          rw [if_neg (by omega), if_pos (by omega)]
        have := hS.2 _ _ hc
        simp only [SrcV, stBit, hs] at this
        rwa [show s.so + (8 * (s.z + i) + t) / 8 = s.so + s.z + i by omega,
          show (8 * (s.z + i) + t) % 8 = t by omega] at this
      have := byte_eq_zero hz
      unfold byteAt at this; rw [dif_pos (show s.so + s.z + i < inp.π.size by
        show _ < inp.π.data.size; omega)] at this
      exact this
    · cases hp
  · cases hp

end N4s
end FR

end G6_FRNodeRun4BR

section G6_FRNodeRun4BS

-- New for `flock-recursive` (IMPC2 §7 step 3; track IMPC2b): the decomposition rows give `StmtBits`; the
-- rows at the seed's ask are among the template's.

/-!
# The decomposition rows' facts

`bitTGB` emits the decomposition rows (`globRows`) once, at the seed's ask (`k = 0`):

* **`seed_rows`**: the program's first ask is the seed's; its template rows are among `askRowsX`'s
  (`first_ask`), so `globRows` holds wherever the template's rows do;
* **`stmtBits_of_glob`**: the statement element rows (`stElRow`) with `PfCells` and Boolean bit cells
  give `StmtBits`: each statement element is its tag part plus `Σ e_j·cell`, so its bits are the cells'
  (`bit_bitsLin`) and the bits no cell takes are zero.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## The rows at the first ask -/

/-- **The first ask's template rows are among `askRowsX`'s** (its ask index is `0`). -/
theorem first_ask (X : Ext) (P : Params) (A : AT) : ∀ (ops : List Op) (cs : CS) (pre : Option Op) {it : Item},
    (ops.filterMap Op.item?).head? = some it →
    ∃ c pre' op, op.item? = some it ∧ ∀ r ∈ A.rows P c pre' op 0, r ∈ askRowsX X P A cs pre 0 ops
  | [], _, _, _, h => by simp at h
  | op :: ops, cs, pre, it, h => by
    rw [askRowsX_cons]
    cases hi : op.item? with
    | some it' =>
      simp only [List.filterMap_cons, hi, List.head?_cons, Option.some.injEq] at h
      subst h
      exact ⟨_, pre, op, hi, fun r hr => List.mem_append_left _ (by rw [if_pos (by simp [hi])]; exact hr)⟩
    | none =>
      simp only [List.filterMap_cons, hi] at h
      obtain ⟨c, pre', op', ho, hr⟩ := first_ask X P A ops _ (some op) h
      refine ⟨c, pre', op', ho, fun r hr0 => List.mem_append_right _ ?_⟩
      convert hr r hr0 using 2
      simp

/-- **`globRows` hold** wherever prototype `π`'s template rows do, when the template has `bitTGB`'s rows. -/
theorem seed_rows {A : AT} {π : ℕ} {T : BTab} {Xa : Ext} {w : Asg}
    (hrA : ∀ c pre op k, ∀ r ∈ bitRowsB T Xa π (protoP π) c pre op k, r ∈ A.rows (protoP π) c pre op k)
    (hask : ∀ r ∈ askRowsP A π, r.Holds w) : ∀ r ∈ globRows T (protoP π) π, r.Holds w := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  obtain ⟨c, pre', op, ho, hm⟩ := first_ask (Xof π) (protoP π) A (protoProg π).ops (CS.init (baseR π)) none
    (it := .seed) (by rw [protoProg_items, hr]; rfl)
  cases op <;> simp only [Op.item?, reduceCtorEq, Option.some.injEq] at ho
  intro r hr0
  exact hask r (hm r (hrA _ _ _ _ r (by simp only [bitRowsB, if_true]; exact hr0)))

/-! ## The statement's bits -/

theorem eBitT_get {j : ℕ} (hj : j < 128) : eBitT.getD j 0 = eBit j := by
  unfold eBitT; simp [hj]

theorem bitsLin_eq {L : List (ℕ × ℕ)} (h : ∀ p ∈ L, p.1 < 128) : bitsLin L = L.map fun p => (p.2, eBit p.1) := by
  unfold bitsLin
  exact List.map_congr_left fun p hp => by rw [eBitT_get (h p hp)]

theorem nodup_fst_filterMap {β : Type} : ∀ (l : List ℕ), l.Nodup → ∀ (f : ℕ → Option (ℕ × β)),
    (∀ j y, f j = some y → y.1 = j) → ((l.filterMap f).map Prod.fst).Nodup
  | [], _, _, _ => List.nodup_nil
  | j :: l, hl, f, hf => by
    have ih := nodup_fst_filterMap l (List.nodup_cons.1 hl).2 f hf
    cases h : f j with
    | none => simpa [List.filterMap_cons, h] using ih
    | some y =>
      rw [List.filterMap_cons, h, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      obtain ⟨z, hz, hz1⟩ := List.mem_map.1 hm
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 hz
      have h1 : y.1 = j := hf j y h
      have h2 : z.1 = a := hf a z hfa
      have : a = j := by rw [← h2, hz1, h1]
      exact (List.nodup_cons.1 hl).1 (this ▸ ha)

theorem tagF_bit (t : UInt8) {j : ℕ} (hj : j < 128) : (tagF t).bit j = (decide (j < 8) && t.toNat.testBit j) := by
  simp only [tagF, F.bit]
  split
  · rw [show t.toUInt64.toNat = t.toNat from UInt8.toNat_toUInt64 t]
    by_cases h8 : j < 8
    · simp [h8]
    · simp only [h8, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le t.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega

theorem byte_eq_of_testBit {x y : UInt8} (h : ∀ t < 8, x.toNat.testBit t = y.toNat.testBit t) : x = y := by
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq; intro t
  by_cases ht : t < 8
  · exact h t ht
  · have hp : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.toNat_lt hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le y.toNat_lt hp)]

/-- **`StmtBits` from the statement element rows** (`globRows`), arena₁'s windows (`PfCells`) and the
bit area's Boolean cells. -/
theorem stmtBits_of_glob {T : BTab} {P : Params} {w : Asg} {π : ℕ} {inp : Input} (hone : P.one.ev w = 1)
    (hpc : PfCells w π inp) (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1)
    (hg : ∀ r ∈ globRows T P π, r.Holds w) : StmtBits T w π inp.π := by
  unfold globRows at hg
  cases hst : T.st with
  | none =>
    simp only [hst] at hg
    exact absurd (hg _ (List.mem_append_right _ List.mem_cons_self)) (failRT_not hone)
  | some s =>
    simp only [hst] at hg
    have hck : 1 ≤ s.z ∧ s.z ≤ s.L ∧ s.L % 16 = 0 ∧ T.stmtB + 8 * s.z ≤ arNb + 8 := by
      by_contra hn
      rw [if_neg hn] at hg
      exact failRT_not hone (hg _ (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)))
    -- the cell bit statement bit `128·kk + j` takes, if any
    let cb : ℕ → Bool := fun b => match T.stCell b with
      | some (some x) => decide (w (bitC π x) = 1)
      | _ => false
    -- element `kk`'s window and its bits
    have hel : ∀ kk < s.L / 16, ∀ j < 128,
        (byteAt inp.π (s.so + 16 * kk + j / 8)).toNat.testBit (j % 8) =
          ((decide (kk = 0) && decide (j < 8) && s.t.toNat.testBit j) ^^ cb (128 * kk + j)) := by
      intro kk hkk j hj
      have hrow := hg (stElRow T P π s kk) (List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.2 ⟨kk, List.mem_range.2 hkk, rfl⟩)))
      unfold stElRow at hrow
      split at hrow
      · rename_i e he
        set L := stCells T π kk with hL
        have hL1 : ∀ p ∈ L, p.1 < 128 ∧ ∃ x, T.stCell (128 * kk + p.1) = some (some x) ∧ p.2 = bitC π x := by
          intro p hp
          obtain ⟨j', hj', hf⟩ := List.mem_filterMap.1 hp
          split at hf
          · rename_i x hx
            cases hf; exact ⟨List.mem_range.1 hj', x, hx, rfl⟩
          · cases hf
        have hLb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1 := by
          intro p hp
          obtain ⟨-, x, hx, hp2⟩ := hL1 p hp
          rw [hp2]
          refine hB x ?_
          simp only [BTab.stCell, hst] at hx
          split_ifs at hx with h1 h2 <;> cases hx
          omega
        have hnd : (L.map Prod.fst).Nodup := nodup_fst_filterMap _ List.nodup_range _ fun j y hy => by
          split at hy
          · cases hy; rfl
          · cases hy
        simp only [Row.Holds, hone, one_mul, ev_subN, Lin.ev_cell] at hrow
        rw [bitsLin_eq fun p hp => (hL1 p hp).1] at hrow
        have hwin : w (arC π e) = F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16) := hpc _ _ he
        have hw2 : F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16) =
            Lin.ev w (if kk = 0 then Lin.smul (tagF s.t) P.one else []) + Lin.ev w (L.map fun p => (p.2, eBit p.1)) := by
          rw [← hwin]; exact sub_eq_iff_eq_add.1 hrow
        have hbyte : (byteAt inp.π (s.so + 16 * kk + j / 8)).toNat.testBit (j % 8) =
            (F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16)).bit j := by
          rw [F.bit_ofBytes _ hj]; simp only [bytesAt, Vector.getElem_ofFn]
        rw [hbyte, hw2, F.bit_add, bit_bitsLin w L hLb (fun p hp => (hL1 p hp).1) hnd j hj]
        have hex : decide (∃ p ∈ L, p.1 = j ∧ w p.2 = 1) = cb (128 * kk + j) := by
          simp only [cb]
          split
          · rename_i x hx
            refine decide_eq_decide.2 ⟨?_, fun hw => ⟨(j, bitC π x), List.mem_filterMap.2 ⟨j, List.mem_range.2 hj,
              by rw [hx]⟩, rfl, hw⟩⟩
            rintro ⟨p, hp, rfl, hw⟩
            obtain ⟨-, x', hx', hp2⟩ := hL1 p hp
            rw [hx] at hx'; cases hx'; rwa [hp2] at hw
          · rename_i hx
            simp only [decide_eq_false_iff_not]
            rintro ⟨p, hp, rfl, -⟩
            obtain ⟨-, x', hx', -⟩ := hL1 p hp
            exact hx x' hx'
        rw [hex]
        congr 1
        split_ifs with hk0
        · subst hk0; simp only [Lin.ev_smul, hone, mul_one, tagF_bit _ hj]; simp
        · simp [F.bit_zero, hk0]
      · exact absurd hrow (failRT_not hone)
    have hcb0 : ∀ b, b < 8 → cb b = false := by
      intro b hb
      simp only [cb, BTab.stCell, hst]
      rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨fun s' hs' => ?_, fun b x hx => ?_⟩
    · cases hs'.symm.trans hst
      apply byte_eq_of_testBit
      intro t ht
      have := hel 0 (by omega) t (by omega)
      rw [show s.so + 16 * 0 + t / 8 = s.so by omega, show t % 8 = t by omega,
        show 128 * 0 + t = t by omega, hcb0 t ht] at this
      rw [this]
      simp [ht]
    · have hx' := hx
      simp only [BTab.stCell, hst] at hx'
      have hb : b < 8 * s.L ∧ 8 ≤ b := by
        split_ifs at hx' with h1 h2 <;> first | omega | simp at hx'
      have hkk : b / 128 < s.L / 16 := by omega
      have := hel (b / 128) hkk (b % 128) (Nat.mod_lt _ (by norm_num))
      rw [show 128 * (b / 128) + b % 128 = b by omega] at this
      have hst8 : stBit T inp.π b = (byteAt inp.π (s.so + 16 * (b / 128) + b % 128 / 8)).toNat.testBit (b % 128 % 8) := by
        simp only [stBit, hst]
        rw [show s.so + b / 8 = s.so + 16 * (b / 128) + b % 128 / 8 by omega, show b % 8 = b % 128 % 8 by omega]
      have htag : (decide (b / 128 = 0) && decide (b % 128 < 8) && s.t.toNat.testBit (b % 128)) = false := by
        by_cases h0 : b / 128 = 0
        · simp [h0, show ¬ b % 128 < 8 by omega]
        · simp [h0]
      rw [htag, Bool.false_xor] at this
      rw [hst8, this]
      cases x with
      | none => simp only [SrcV, cb, hx]
      | some c =>
        simp only [SrcV, cb, hx]
        have hc : c < arNb := by
          split_ifs at hx' with h1 h2 <;> first | (simp only [Option.some.injEq] at hx'; omega) | simp at hx'
        first
          | done
          | (rcases hB c hc with h0 | h0 <;> simp [h0, Circ.bitF])

/-! ## The answers' bits -/

/-- A kind using an answer gets every one of its 256 bits a cell. -/
theorem ansCell_some {T : BTab} {ι : Kind} {k j x : ℕ} (h : T.ansCell ι k j = some x) {j' : ℕ} (hj' : j' < 256) :
    (T.ansCell ι k j').isSome = true := by
  unfold BTab.ansCell at h ⊢
  split at h
  · rename_i i q g hk
    dsimp only at h ⊢
    split_ifs at h with h1 h2 <;> (rw [if_pos ⟨h1.1, hj'⟩]; split <;> rfl)
  · cases h

theorem ansCell_lt {T : BTab} {ι : Kind} {k j x : ℕ} (h : T.ansCell ι k j = some x) :
    j < 256 ∧ ∃ i q g, T.ans.getD k none = some (i, q, g) := by
  unfold BTab.ansCell at h
  split at h
  · rename_i i q g hk
    dsimp only at h
    split_ifs at h with h1 h2 <;> exact ⟨h1.2, i, q, g, hk⟩
  · cases h

/-- **Each kind's map has a class representative** (`ansRows`' `cls`) whose class contains it. -/
theorem cls_ex {α : Type} [DecidableEq α] (ok : Kind → Bool) (m : Kind → α) (ι : Kind) (h : ok ι = true) :
    ∃ ι' ∈ kinds.filter (fun ι' => ok ι' && !(kinds.any fun κ => decide (kix κ < kix ι') && ok κ &&
        decide (m κ = m ι'))), m ι' = m ι ∧ (kinds.filter fun κ => ok κ && decide (m κ = m ι')).contains ι = true := by
  cases ι
  · exact ⟨.L32, by simp [kinds, kix, h], rfl, by simp [kinds, h]⟩
  · by_cases hL : ok .L32 = true ∧ m .L32 = m .P30
    · exact ⟨.L32, by simp [kinds, kix, hL.1], hL.2, by simp [kinds, h, hL.2]⟩
    · refine ⟨.P30, ?_, rfl, by simp [kinds, h]⟩
      simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil, h]
      split_ifs <;> simp_all
  · by_cases hL : ok .L32 = true ∧ m .L32 = m .N30
    · exact ⟨.L32, by simp [kinds, kix, hL.1], hL.2, by simp [kinds, h, hL.2]⟩
    · by_cases hP : ok .P30 = true ∧ m .P30 = m .N30
      · refine ⟨.P30, ?_, hP.2, by simp [kinds, h, hP.2]⟩
        have : ¬ (ok .L32 = true ∧ m .L32 = m .P30) := fun h' => hL ⟨h'.1, h'.2.trans hP.2⟩
        simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil]
        split_ifs <;> simp_all
      · refine ⟨.N30, ?_, rfl, by simp [kinds, h]⟩
        simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil]
        split_ifs <;> simp_all

theorem nodup_zipIdx_filterMap (g : ℕ → ℕ) : ∀ (l : List (Option ℕ)) (n : ℕ),
    (((l.zipIdx n).filterMap fun p => p.1.map fun x => (p.2, g x)).map Prod.fst).Nodup ∧
      ∀ q ∈ ((l.zipIdx n).filterMap fun p => p.1.map fun x => (p.2, g x)).map Prod.fst, n ≤ q
  | [], _ => by simp
  | a :: l, n => by
    obtain ⟨ih1, ih2⟩ := nodup_zipIdx_filterMap g l (n + 1)
    rw [List.zipIdx_cons]
    cases a with
    | none =>
      simp only [List.filterMap_cons, Option.map_none]
      exact ⟨ih1, fun q hq => by have := ih2 q hq; omega⟩
    | some x =>
      simp only [List.filterMap_cons, Option.map_some, List.map_cons, List.nodup_cons, List.mem_cons]
      refine ⟨⟨fun hm => by have := ih2 n hm; omega, ih1⟩, fun q hq => ?_⟩
      rcases hq with rfl | hq
      · exact le_refl _
      · have := ih2 q hq; omega

/-- **One answer half's decomposition rows** (`ansRows`, half `c` on arena₁'s element `el`): a cell the
selected kind's map gives for bit `128c + j` is bit `j` of the element. -/
theorem ans_half {T : BTab} {P : Params} {w : Asg} {π k el c : ℕ} {ι : Kind} (hP : SelOk w P ι)
    (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1) (hR : ∀ r ∈ ansRows T P π k el c, r.Holds w)
    {j : ℕ} (hj : j < 128) {x : ℕ} (hx : T.ansCell ι k (128 * c + j) = some x) :
    w (bitC π x) = if (w (arC π el)).bit j then 1 else 0 := by
  unfold ansRows at hR
  simp only [kt_eq] at hR
  set m : Kind → List (Option ℕ) := fun ι => (List.range 128).map fun j => T.ansCell ι k (128 * c + j) with hm
  have hbound : (kinds.all fun ι => (m ι).all fun x => x.all (· < arNb)) = true := by
    by_contra hn
    rw [if_neg hn] at hR
    exact failRT_not hP.1 (hR _ (List.mem_append_left _ List.mem_cons_self))
  rw [if_pos hbound, List.nil_append] at hR
  have hok : ((m ι).all Option.isSome) = true := by
    rw [List.all_eq_true]; intro y hy
    simp only [hm] at hy
    obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hy
    exact ansCell_some hx (by have := (ansCell_lt hx).1; have := List.mem_range.1 hj'; omega)
  obtain ⟨ι', hι', hmι, hcon⟩ := cls_ex (fun ι => (m ι).all Option.isSome) m ι hok
  have hrow := hR _ (List.mem_map.2 ⟨ι', hι', rfl⟩)
  try dsimp only at hrow
  have hlin : ∀ a : Lin, (a.ev w = 1) →
      (⟨a, subN (Lin.cell (arC π el)) (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))), []⟩ : Row).Holds w →
      w (arC π el) = Lin.ev w (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))) := by
    intro a ha hh
    simp only [Row.Holds, ha, one_mul, ev_subN, Lin.ev_cell, Lin.ev_nil] at hh
    exact sub_eq_zero.1 hh
  have heq : w (arC π el) = Lin.ev w (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))) := by
    split_ifs at hrow
    · exact hlin _ hP.1 hrow
    · simp only [hm] at hcon
      exact hlin _ (by simp only [gateS_ev hP, hcon]; rfl) hrow
  rw [hmι] at heq
  set L := ((m ι).zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x) with hL
  have hmemL : ∀ p ∈ L, p.1 < 128 ∧ ∃ y, T.ansCell ι k (128 * c + p.1) = some y ∧ p.2 = bitC π y := by
    intro p hp
    obtain ⟨q, hq, hf⟩ := List.mem_filterMap.1 hp
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hq
    simp only [List.length_zipIdx, hm, List.length_map, List.length_range] at hi
    have hq1 : q.1 = (m ι)[i]'(by simp [hm]; omega) := by rw [← he]; simp
    have hq2 : q.2 = i := by rw [← he]; simp
    refine ⟨by rw [hq2]; exact hi, y, ?_, rfl⟩
    rw [← hy, hq1, hq2]; simp [hm]
  have hLb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1 := by
    intro p hp
    obtain ⟨-, y, hy, hp2⟩ := hmemL p hp
    rw [hp2]
    refine hB y ?_
    have := List.all_eq_true.1 hbound ι (by cases ι <;> simp [kinds])
    have := List.all_eq_true.1 this (some y) (by
      rw [← hy]; simp only [hm]; exact List.mem_map.2 ⟨_, List.mem_range.2 (hmemL p hp).1, rfl⟩)
    simpa using this
  have hnd := (nodup_zipIdx_filterMap (bitC π) (m ι) 0).1
  rw [bitsLin_eq fun p hp => (hmemL p hp).1] at heq
  have hjx : (j, bitC π x) ∈ L := by
    refine List.mem_filterMap.2 ⟨((m ι)[j]'(by simp [hm, hj]), j), ?_, ?_⟩
    · rw [List.mem_iff_getElem?]; exact ⟨j, by simp [List.getElem?_zipIdx, hm, hj]⟩
    · simp [hm, hx]
  exact decomp_cell w L hLb (fun p hp => (hmemL p hp).1) hnd heq hjx

theorem ans_fold_mem : ∀ (l : List ((ℕ × ℕ × ℕ) × ℕ)) (acc : Array (Option (ℕ × ℕ × ℕ))) (k : ℕ) (v : ℕ × ℕ × ℕ),
    (l.foldl (fun a p => a.set! p.1.1 (some (p.1.2.1, p.1.2.2, p.2))) acc).getD k none = some v →
    acc.getD k none = some v ∨ ∃ p ∈ l, p.1.1 = k
  | [], _, _, _, h => Or.inl h
  | p :: l, acc, k, v, h => by
    rw [List.foldl_cons] at h
    rcases ans_fold_mem l _ k v h with h1 | ⟨q, hq, hqk⟩
    · by_cases hk : p.1.1 = k
      · exact Or.inr ⟨p, List.mem_cons_self, hk⟩
      · left
        simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hk] at h1
        simpa [Array.getD_eq_getD_getElem?] using h1
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqk⟩

/-- **A table's answer places are `ansList`'s** (`mkTab`). -/
theorem mkTab_ans {ops : List Op} {G : Grp} {k : ℕ} {v : ℕ × ℕ × ℕ} (h : (mkTab ops G).ans.getD k none = some v) :
    ∃ a ∈ ansList, a.1 = k := by
  simp only [mkTab] at h
  rcases ans_fold_mem _ _ k v h with h1 | ⟨p, hp, hpk⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h1
    split at h1 <;> simp at h1
  · have := List.mem_map_of_mem (f := Prod.fst) hp
    rw [List.zipIdx_map_fst] at this
    exact ⟨p.1, this, hpk⟩

/-- **`PosBits` from the answer decomposition rows** (`globRows`), arena₁'s answer halves (`hA`) and the
bit area's Boolean cells. -/
theorem posBits_of_glob {T : BTab} {P : Params} {w : Asg} {π : ℕ} {ι : Kind} {tr : Trace} (hP : SelOk w P ι)
    (hans : ∀ k v, T.ans.getD k none = some v → ∃ a ∈ ansList, a.1 = k)
    (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1) (hg : ∀ r ∈ globRows T P π, r.Holds w)
    (hA : ∀ k it e, itemsT[k]? = some it → tr[k]? = some e →
      w (arC π (aElT k it)) = dlo e.2 ∧ w (arC π (aElT k it + 1)) = dhi e.2) :
    PosBits T w π ι tr := by
  intro k j x e hx he
  obtain ⟨hj, i, q, g, hk⟩ := ansCell_lt hx
  obtain ⟨a, ha, rfl⟩ := hans _ _ hk
  have hga : ∀ r ∈ (match itemsT[a.1]? with
      | some it => ansRows T P π a.1 (aElT a.1 it) 0 ++ ansRows T P π a.1 (aElT a.1 it + 1) 1
      | none => [failRT P]), r.Holds w := fun r hr =>
    hg r (List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha, hr⟩))
  split at hga
  · rename_i it hit
    obtain ⟨hlo, hhi⟩ := hA _ _ _ hit he
    by_cases hc : j < 128
    · have := ans_half hP hB (fun r hr => hga r (List.mem_append_left _ hr)) hc (c := 0) (by simpa using hx)
      rw [this, hlo, bit_dlo _ hc]; rfl
    · have := ans_half hP hB (fun r hr => hga r (List.mem_append_right _ hr)) (j := j - 128) (by omega) (c := 1)
        (by rw [show 128 * 1 + (j - 128) = j by omega]; exact hx)
      rw [this, hhi, bit_dhi _ (by omega), show 128 + (j - 128) = j by omega]; rfl
  · exact absurd (hga _ List.mem_cons_self) (failRT_not hP.1)

end N4s
end FR

end G6_FRNodeRun4BS
