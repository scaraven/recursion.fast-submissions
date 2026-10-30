-- New for `flock-recursive` (IMPC2 §7 step 3 item 2; track IMPC2b): the bits' run proofs — `bitOf`'s imports,
-- `bits n`'s auxiliary cells and the statement's two flags (tag, zero tail) on the answer-driven run; `SlotRunB`.
import FRNodeRun4BL
import FRNodeRows4AskIR

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
  simp only [stepOut] at ha
  cases hx : Xof π P cs op with
  | none => rw [hx, Option.getD_none, opOut_aux] at ha; cases ha
  | some o =>
    rw [hx, Option.getD_some] at ha
    simp only [Xof, tplExt4, Ext.orElse] at hx
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
