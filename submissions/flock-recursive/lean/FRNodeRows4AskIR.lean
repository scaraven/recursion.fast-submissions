-- New for `flock-recursive` (SRA-RESULT §6.2–§6.3; ASK-P-RESULT §6.2; track IMPC): register provenance
-- along the answer-driven run, the zero-pinned foreign flags and the column words of `SlotRunA`.
import FRNodeRows4AskIS

/-!
# `SlotRunA` with the zero pins and the column words

`SlotRunA`'s auxiliary and foreign facts are about the answer-driven run's registers. Their operands
are byte registers (`piField`s, untracked), so the rows alone do not reach them; here:

* **`execA_prov`** (register provenance, a fact about `execA`, no program evaluated): on any
  answer-driven run, a register a `piField f o len` appended (`provL`) holds the proof's bytes
  `[absOff f o, absOff f o + len)`.
* **`trail_fors`**, **`trail_aux`**: a foreign flag (an auxiliary import) of the compile is at a point of
  the compile's trail whose register count is the flag's, and whose template rows `askRowsX` holds.
* **`flag_zpin`**: a foreign `assertZero` on a `piField`'s bytes whose windows are elements, with the
  zero pins (`zRows`) holding, is `true`; **`aux_col`**: a `felems` auxiliary import on such a register,
  with `colRows` holding, holds.
* **`slotRunA_of_impc`** / **`slotRunA_of_col`**: `SlotRunA` from the template's rows, `PfCells` and the
  residual (the flags not `zPin`, the auxiliary imports not `colOk`, the residual imports).
* **`gap4Imp_of_impcR`**: SRA's `gap4Imp_of_rsv` with `impcTG` and `colTG` beside the reserve, the residual
  run facts restricted accordingly.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## Register counts and provenance -/

theorem evalOp_len {impl : OpImpl} {κ : Kind} {inp : Input} {regs : Array Val} {op : Op} {vs : List Val}
    {ok : Bool} (h : evalOp impl κ inp regs op = .vals vs ok) : vs.length = op.outs := by
  cases op <;> simp only [evalOp, Res.vals.injEq, reduceCtorEq] at h <;> obtain ⟨rfl, -⟩ := h <;> rfl

theorem ask_outs {impl : OpImpl} {κ : Kind} {inp : Input} {regs : Array Val} {op : Op} {q : ByteArray}
    (h : evalOp impl κ inp regs op = .ask q) : op.outs = 1 := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

/-- **Register provenance** along the answer-driven run: a register a `piField f o len` appended holds
the proof's bytes. -/
theorem execA_prov {impl : OpImpl} {κ : Kind} {inp : Input} : ∀ (ops : List Op) (s0 : St) (tr : Trace)
    {s : St} {tr' : Trace}, execA impl κ inp ops s0 tr = some (s, tr') → ∀ {r f o len : ℕ},
      (r, f, o, len) ∈ provL s0.regs.size ops → s.regs[r]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len)))
  | [], _, _, _, _, _, _, _, _, _, hm => by simp [provL] at hm
  | op :: ops, s0, tr, s, tr', he, r, f, o, len, hm => by
    simp only [provL, List.mem_append] at hm
    simp only [execA] at he
    split at he
    · next vs ok hv =>
      rcases hm with hm | hm
      · cases op <;> simp only [List.mem_singleton, List.not_mem_nil, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
        simp only [evalOp, Res.vals.injEq] at hv
        obtain ⟨rfl, -⟩ := hv
        obtain ⟨more, hmore⟩ := execA_prefix ops _ _ he
        rw [hmore]
        simp only [Array.append_singleton]
        rw [Array.getElem?_append_left (by simp)]
        simp
      · have hs : (s0.regs ++ vs.toArray).size = s0.regs.size + op.outs := by
          simp [evalOp_len hv]
        exact execA_prov ops _ tr he (by rw [hs]; exact hm)
    · next q hq =>
      rcases tr with _ | ⟨⟨q', a⟩, tr0⟩
      · cases he
      · rcases hm with hm | hm
        · cases op <;> simp only [List.mem_singleton, List.not_mem_nil, Prod.mk.injEq] at hm
          simp [evalOp] at hq
        · exact execA_prov ops _ tr0 he (by rw [Array.size_push, ← ask_outs hq]; exact hm)

theorem provOf_mem {pv : List (ℕ × ℕ × ℕ × ℕ)} {r f o len : ℕ} (h : provOf pv r = some (f, o, len)) :
    (r, f, o, len) ∈ pv := by
  unfold provOf at h
  obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hx
  have h1 : x.1 = r := by simpa using List.find?_some hx
  obtain ⟨x1, x2⟩ := x
  simp only at h1 he
  subst h1 he
  exact hm

/-! ## The compile's flags and auxiliary imports along the trail -/

theorem align_fors (cs : CS) (x : Option (ℕ × ℕ)) : (cs.align x).fors = cs.fors := by cases x <;> rfl
theorem align_aux (cs : CS) (x : Option (ℕ × ℕ)) : (cs.align x).aux = cs.aux := by cases x <;> rfl

/-- **A foreign flag of the compile is at a trail point** with its register count, whose template rows
are in `askRowsX`. -/
theorem trail_fors (X : Ext) (P : Params) (A : AT) : ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ)
    {p : Op × ℕ}, p ∈ (compileFromX X P cs ops).fors → p ∈ cs.fors ∨ ∃ (c : CS) (pre' : Option Op) (k' : ℕ),
      c.slots.size = p.2 ∧ (A.cov p.1 = true → ∀ r ∈ A.rows P c pre' p.1 k', r ∈ askRowsX X P A cs pre k ops)
  | [], _, _, _, _, h => Or.inl h
  | op :: ops, cs, pre, k, p, h => by
    simp only [compileFromX] at h
    rcases trail_fors X P A ops _ (some op) (if op.item?.isSome then k + 1 else k) h with h1 | ⟨c, pre', k', hc, hr⟩
    · simp only [CS.add, align_fors] at h1
      split_ifs at h1
      · rcases List.mem_cons.1 h1 with rfl | h1
        · right
          refine ⟨cs.align (alignOf op ops), pre, k, rfl, fun hcov r hr => ?_⟩
          rw [askRowsX_cons]
          exact List.mem_append_left _ (by rw [if_pos (by simp [hcov])]; exact hr)
        · exact Or.inl h1
      · exact Or.inl h1
    · exact Or.inr ⟨c, pre', k', hc, fun hcov r hr0 => by
        rw [askRowsX_cons]; exact List.mem_append_right _ (hr hcov r hr0)⟩

/-- **An auxiliary import of the compile is at a trail point** (of the op whose output carries it). -/
theorem trail_aux (X : Ext) (P : Params) (A : AT) : ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ)
    {a : (List Lin × ℕ × AuxK) × ℕ}, a ∈ (compileFromX X P cs ops).aux → a ∈ cs.aux ∨
      ∃ (c : CS) (pre' : Option Op) (k' : ℕ) (op : Op), c.slots.size = a.2 ∧ a.1 ∈ (stepOut X P c op).aux ∧
        (A.cov op = true → ∀ r ∈ A.rows P c pre' op k', r ∈ askRowsX X P A cs pre k ops)
  | [], _, _, _, _, h => Or.inl h
  | op :: ops, cs, pre, k, a, h => by
    simp only [compileFromX] at h
    rcases trail_aux X P A ops _ (some op) (if op.item?.isSome then k + 1 else k) h with h1 | ⟨c, pre', k', op', hc, hm, hr⟩
    · simp only [CS.add, align_aux, List.mem_append, List.mem_map] at h1
      rcases h1 with ⟨x, hx, rfl⟩ | h1
      · right
        refine ⟨cs.align (alignOf op ops), pre, k, op, rfl, hx, fun hcov r hr => ?_⟩
        rw [askRowsX_cons]
        exact List.mem_append_left _ (by rw [if_pos (by simp [hcov])]; exact hr)
      · exact Or.inl h1
    · exact Or.inr ⟨c, pre', k', op', hc, hm, fun hcov r hr0 => by
        rw [askRowsX_cons]; exact List.mem_append_right _ (hr hcov r hr0)⟩

/-! ## Zero bytes from zero cells -/

theorem toBytes_zero : F.toBytes 0 = Vector.replicate 16 0 := by decide

theorem bytesAt_zero {q : ByteArray} {x : ℕ} (h : F.ofBytes (bytesAt q x 16) = 0) : bytesAt q x 16 = Vector.replicate 16 0 := by
  rw [← F.toBytes_ofBytes (bytesAt q x 16), h, toBytes_zero]

/-- The extract of a byte array is zero where every window `[x + 16t, x + 16t + 16)` is. -/
theorem extract_zero {q : ByteArray} {x len : ℕ} (hl : len % 16 = 0)
    (h : ∀ t < len / 16, bytesAt q (x + 16 * t) 16 = Vector.replicate 16 0) :
    (q.extract x (x + len)).data.all (· == 0) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < min (x + len) q.data.size - x := by simpa [ByteArray.data_extract, Array.size_extract] using hi
  have hi1 : i < len := by omega
  have hi2 : x + i < q.size := by show x + i < q.data.size; omega
  have ht := h (i / 16) (by omega)
  have hv := congrArg (fun v : Vector UInt8 16 => v[i % 16]'(Nat.mod_lt _ (by norm_num))) ht
  simp only [bytesAt, Vector.getElem_ofFn, Vector.getElem_replicate] at hv
  rw [show x + 16 * (i / 16) + i % 16 = x + i by omega] at hv
  simp only [ByteArray.data_extract, Array.getElem_extract, beq_iff_eq]
  unfold byteAt at hv
  rw [dif_pos hi2] at hv
  exact hv

theorem rd_extract {regs : Array Val} {a n : ℕ} (h : a < n) : rd (regs.extract 0 n) a = rd regs a := by
  unfold rd
  by_cases ha : a < regs.size
  · rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem?_eq_getElem ha, Array.getElem_extract]; simp
  · rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]

/-- **A zero-pinned foreign flag is `true`**: the operand is a `piField`'s bytes (`hreg`), its windows
are elements whose arena₁ cells hold them (`PfCells`), and the pins hold. -/
theorem flag_zpin {impl : OpImpl} {ι : Kind} {inp : Input} {regs : Array Val} {P : Params} {w : Asg} {π : ℕ}
    {a n f o len : ℕ} {act : KC Bool} (hsel : SelOk w P ι) (hpc : PfCells w π inp) (hw : winsOk f o len = true)
    (hreg : regs[a]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len)))) (han : a < n)
    (hrows : ∀ t < len / 16, ∀ e, winE (absOff f o + 16 * t) = some e →
      (P.gate act).ev w * w (π * slotM4 + arA1 + e) = 0) :
    flagOf impl ι inp (regs.extract 0 n) (.assertZero a act) = true := by
  simp only [flagOf, evalOp]
  cases hact : act ι
  · rfl
  · have hrd : rd (regs.extract 0 n) a = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
      rw [rd_extract han, rd, hreg]; rfl
    rw [hrd]
    simp only [winsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Option.isSome_iff_exists] at hw
    obtain ⟨⟨hl, -⟩, hwin⟩ := hw
    simp only [Bool.not_true, Bool.false_or, Val.isZero]
    refine extract_zero hl fun t ht => bytesAt_zero ?_
    obtain ⟨e, he⟩ := hwin t ht
    have := hrows t ht e he
    rw [gate_ev hsel, hact, show Circ.bitF true = (1 : F) from rfl, one_mul] at this
    rw [← hpc _ _ he, this]

/-- **A `felems` auxiliary import on a `piField`'s bytes holds** where `colRows` holds. -/
theorem aux_col {regs : Array Val} {P : Params} {w : Asg} {π : ℕ} {inp : Input} {pv : List (ℕ × ℕ × ℕ × ℕ)}
    {cells : List Lin} {r n sz f o len : ℕ} (hone : P.one.ev w = 1) (hpc : PfCells w π inp)
    (hpr : provOf pv r = some (f, o, len)) (hw : winsOk f o len = true)
    (hsz : absOff f o + len ≤ inp.π.size)
    (hreg : regs[r]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len)))) (hrs : r < sz)
    (hcl : cells.length = n) (hrows : ∀ x ∈ colRows P π pv sz cells r n, x.Holds w) :
    cells.map (Lin.ev w) = (AuxK.felems n).val (rd (regs.extract 0 sz) r) := by
  have hrd : rd (regs.extract 0 sz) r = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
    rw [rd_extract hrs, rd, hreg]; rfl
  rw [hrd]
  unfold colRows at hrows
  rw [hpr] at hrows
  dsimp only at hrows
  rw [if_pos ⟨hcl, hrs, hw⟩] at hrows
  simp only [winsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Option.isSome_iff_exists] at hw
  obtain ⟨⟨hl, -⟩, hwin⟩ := hw
  have hsize : (inp.π.extract (absOff f o) (absOff f o + len)).size = len := by
    simp [ByteArray.size_extract]; omega
  refine List.ext_getElem (by simp [AuxK.val, hcl]) fun b h1 h2 => ?_
  simp only [List.length_map] at h1
  simp only [List.getElem_map, AuxK.val, List.getElem_range, Val.toB]
  have hmem : (cells[b], b) ∈ cells.zipIdx := by
    rw [List.mem_iff_getElem?]; exact ⟨b, by simp [List.getElem?_zipIdx, h1]⟩
  rw [felems, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hsize]
  by_cases hb : b < len / 16
  · obtain ⟨e, he⟩ := hwin b hb
    have hh := hrows (a1Row P π cells[b] e) (List.mem_filterMap.2 ⟨(cells[b], b), hmem, by simp [hb, he]⟩)
    simp only [a1Row, Row.Holds, Lin.ev_sub, Lin.ev_cell, hone, one_mul, Lin.ev_nil] at hh
    rw [sub_eq_zero.1 hh, hpc _ _ he, if_pos hb, Option.map_some, Option.getD_some]
    refine congrArg F.ofBytes (Vector.ext fun t ht => ?_)
    simp only [bytesAt, Vector.getElem_ofFn]
    rw [byteAt_extract _ _ _ (by omega), Nat.add_assoc]
  · have hh := hrows ⟨P.one, cells[b], []⟩ (List.mem_filterMap.2 ⟨(cells[b], b), hmem, by simp [hb]⟩)
    simp only [Row.Holds, hone, one_mul, Lin.ev_nil] at hh
    rw [hh, if_neg hb]
    rfl

/-! ## Which ops carry `felems` auxiliary imports -/

theorem opOut_aux (P : Params) (cs : CS) (op : Op) : (opOut P cs op).aux = [] := by
  cases op <;> simp only [opOut, imports, skip, muxOut, eqTensor] <;> (repeat' split) <;> rfl

theorem tplExt_felems {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out} (h : tplExt tc P cs op = some o)
    {a : List Lin × ℕ × AuxK} (ha : a ∈ o.aux) {n : ℕ} (hn : a.2.2 = .felems n) : isDotKF op = true := by
  cases op
  case dotKF => rfl
  all_goals (simp only [tplExt] at h; repeat' (first | (split at h) | (split_ifs at h)))
  all_goals (cases h <;> first | (simp [tplOut] at ha; done) | (simp at ha; subst ha; simp at hn))

theorem tplExtKM_felems {F : TFilt} {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out}
    (h : tplExtKM F tc P cs op = some o) {a : List Lin × ℕ × AuxK} (ha : a ∈ o.aux) {n : ℕ}
    (hn : a.2.2 = .felems n) : isDotKF op = true := by
  cases op
  all_goals (simp only [tplExtKM] at h; repeat' (first | (split at h) | (split_ifs at h)))
  all_goals (cases h <;> first | (simp [tplOut] at ha; done) | (simp at ha; subst ha; simp at hn))

theorem extGetK_aux {P : Params} {cs : CS} {op : Op} {o : Out} (h : extGetK P cs op = some o) : o.aux = [] := by
  cases op <;> simp only [extGetK, reduceCtorEq] at h
  split_ifs at h
  cases h; rfl

/-- **Only a `dotKF` carries a `felems` auxiliary import** (prototype `π`'s compile). -/
theorem xof_felems {π : ℕ} {P : Params} {cs : CS} {op : Op} {a : List Lin × ℕ × AuxK}
    (ha : a ∈ (stepOut (Xof π) P cs op).aux) {n : ℕ} (hn : a.2.2 = .felems n) : isDotKF op = true := by
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
        exact tplExt_felems h5 ha hn
    | none =>
      rw [h4, Option.orElse_none] at hx
      split_ifs at hx
      cases h6 : tplExtKM (protoF π) (protoLay π).ctx P cs op with
      | some o' =>
        rw [h6, Option.orElse_some, Option.some.injEq] at hx
        subst hx; exact tplExtKM_felems h6 ha hn
      | none =>
        rw [h6, Option.orElse_none] at hx
        rw [extGetK_aux hx] at ha; cases ha

/-! ## `SlotRunA` -/

/-- **The flags the zero pins discharge**: a foreign `assertZero` on a `piField`'s bytes (register
before the flag's count) whose windows are elements. -/
def zPin (pv : List (ℕ × ℕ × ℕ × ℕ)) (p : Op × ℕ) : Bool :=
  match p.1 with
  | .assertZero a _ =>
    match provOf pv a with
    | some (f, o, len) => decide (a < p.2) && winsOk f o len
    | none => false
  | _ => false

/-- **The auxiliary imports `colTG` binds**: `felems n` on such a register, `n` cells. -/
def colOk (pv : List (ℕ × ℕ × ℕ × ℕ)) (a : (List Lin × ℕ × AuxK) × ℕ) : Bool :=
  match a.1.2.2 with
  | .felems n =>
    match provOf pv a.1.2.1 with
    | some (f, o, len) => decide (a.1.1.length = n) && decide (a.1.2.1 < a.2) && winsOk f o len
    | none => false
  | .bits _ => false

/-- Prototype `π`'s `piField` registers. -/
def pvP (π : ℕ) : List (ℕ × ℕ × ℕ × ℕ) := provLT 0 (protoProg π).ops

theorem slotπ_size (κ : NodeKind) (v : ℕ) (w : Asg) : ((rd4 X.pf4).slotπ κ v w).size = piSizeOf seq4 := by
  show (⟨(slotPf X.pf4 κ v w).toArray⟩ : ByteArray).size = _
  simp [ByteArray.size, slotPf, fitL_length]

/-- **The residual run facts** (`SlotRunA` less the zero-pinned flags and the bound column words). -/
def SlotRunI (rt : RT) (A : AT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∀ s : St, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
    (∀ a ∈ (protoCS π).aux, colOk (pvP π) a = false →
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ impAP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, zPin (pvP π) p = false → flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **`SlotRunA` from the template's rows**: with `impcTG`'s and `colTG`'s rows among the template's
(`hrI`, `hrC`), the rows holding at the slot (`hask`) and arena₁ holding the proof's windows, only the
residual run facts are left. -/
theorem slotRunA_of_impc {rt : RT} {A : AT} {impl : OpImpl} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace}
    {w : Asg} (hcI : ∀ op, impcCov op = true → A.cov op = true)
    (hrI : ∀ P c pre op k, ∀ r ∈ impcRows (Xof π) π (pvP π) P c op, r ∈ A.rows P c pre op k)
    (hcC : ∀ op, isDotKF op = true → A.cov op = true)
    (hrC : ∀ P c pre op k, ∀ r ∈ (colTG (Xof π) π (pvP π)).rows P c pre op k, r ∈ A.rows P c pre op k)
    (hsel : SelOk w (protoP π) ι) (hask : ∀ r ∈ askRowsP A π, r.Holds w) (hpc : PfCells w π inp)
    (hsz : inp.π.size = piSizeOf seq4) (hres : SlotRunI rt A impl π ι inp tr w) :
    SlotRunA rt A impl π ι inp tr w := by
  intro s he
  obtain ⟨hx, hi, hf⟩ := hres s he
  have hone := hsel.1
  have hprov : ∀ {r f o len}, provOf (pvP π) r = some (f, o, len) →
      s.regs[r]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len))) := fun hp =>
    execA_prov _ _ _ he (by rw [← provLT_eq]; exact provOf_mem hp)
  refine ⟨fun a ha => ?_, hi, fun p hp => ?_⟩
  · cases hc : colOk (pvP π) a
    · exact hx a ha hc
    · rcases trail_aux (Xof π) (protoP π) A _ _ none 0 ha with h0 | ⟨c, pre', k', op, hcs, hm, hr⟩
      · cases h0
      obtain ⟨⟨cells, r, kd⟩, m⟩ := a
      cases kd with
      | bits _ => simp [colOk] at hc
      | felems n =>
        simp only [colOk] at hc
        split at hc
        · rename_i f o len hpr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨hcl, hrm⟩, hw⟩ := hc
          have hdot := xof_felems hm rfl
          have hrows : ∀ x ∈ colRows (protoP π) π (pvP π) c.slots.size cells r n, x.Holds w := by
            intro x hx0
            refine hask x (hr (hcC op hdot) x (hrC _ _ _ _ _ x ?_))
            have himp : (stepOut (Xof π) (protoP π) c op).imp = false := by
              cases h : (stepOut (Xof π) (protoP π) c op).imp
              · rfl
              · exfalso
                have := hask _ (hr (hcC op hdot) _ (hrC _ _ _ _ _ _ (by
                  simp only [colTG, hdot, h, if_true]; exact List.mem_singleton_self _)))
                exact failRT_not hone this
            simp only [colTG, hdot, himp, if_true, Bool.false_eq_true, if_false]
            obtain ⟨l, t, hl⟩ := List.mem_iff_append.1 hm
            rw [hl]
            clear hl
            induction l with
            | nil => simp only [List.nil_append, auxRows]; exact List.mem_append_left _ hx0
            | cons y l ih =>
              obtain ⟨y1, y2, y3⟩ := y
              cases y3 <;> simp only [List.cons_append, auxRows] <;> [exact List.mem_append_right _ ih; exact ih]
          have hw' := hw
          simp only [winsOk, Bool.and_eq_true, decide_eq_true_eq] at hw'
          exact aux_col hone hpc hpr hw (by rw [hsz]; exact hw'.1.2) (hprov hpr) (by simpa using hrm) hcl
            (by rw [← hcs]; exact hrows)
        · cases hc
  · cases hz : zPin (pvP π) p
    · exact hf p hp hz
    · rcases trail_fors (Xof π) (protoP π) A _ _ none 0 hp with h0 | ⟨c, pre', k', hcs, hr⟩
      · cases h0
      obtain ⟨op, m⟩ := p
      cases op with
      | assertZero a act =>
        simp only [zPin] at hz
        split at hz
        · rename_i f o len hpr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
          obtain ⟨ham, hw⟩ := hz
          have hcov := hcI (.assertZero a act) rfl
          have hrow : ∀ x ∈ impcRows (Xof π) π (pvP π) (protoP π) c (.assertZero a act), x.Holds w :=
            fun x hx0 => hask x (hr hcov x (hrI _ _ _ _ _ x hx0))
          simp only [impcRows] at hrow
          split_ifs at hrow with himp
          · exact absurd (hrow _ List.mem_cons_self) (failRT_not hone)
          · simp only [zRows, hpr] at hrow
            rw [if_pos ⟨by simpa [hcs] using ham, hw⟩] at hrow
            refine flag_zpin hsel hpc hw (hprov hpr) ham fun t ht e he0 => ?_
            have := hrow _ (List.mem_filterMap.2 ⟨t, List.mem_range.2 ht, by rw [he0]; rfl⟩)
            simpa [Row.Holds] using this
        · cases hz
      | _ => simp [zPin] at hz

/-! ## `imp` with the import classes, the zero pins and the column words -/

/-- Prototype `π`'s template: `withImpc` (the ask template, `input`, the reserve, the import classes),
then the column words. -/
def withImpcC (Aq : ℕ → AT) (π : ℕ) : AT := (withImpc Aq π).add (colTG (Xof π) π (pvP π)).toAT

/-- **`imp` with `impcTG` and `colTG`**: what remains per active slot and selectable index is the ask
template's `ATOk` and the residual run facts `SlotRunI` (the auxiliary imports other than the bound
column words, the residual imports, the foreign flags other than the zero-pinned ones). -/
theorem gap4Imp_of_impcR {rt : ℕ → RT} {Aq : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (hpf : PfHdr X.pf4)
    (hpv : PfView X.pf4) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {ch : List F} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withImpcC Aq) κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (Aq (protoOf κ v)) ι
          (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) (slotAsg κ v w) ((rd4 X.pf4).slotTr κ v w) ∧
        SlotRunI (rt (protoOf κ v)) (withImpcC Aq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) :=
  gap4Imp_of_runS hT₀ hT hok hpf hpv hfoldR hfoldA hS.1 fun v hv ι hι =>
    ⟨atOk_add (atOk_add (atOk_add (atOk_add (h v hv ι hι).1
        (atImp_inp (inpCells_of_rows hpv hpf hS.1 v hv ι hι))) (atImp_rsv_slot hS.2.1 hS.2.2 v ι _))
        (atImp_impc (pfCells_of_rows hS.1 hv))) atImp_col,
      slotRunA_of_impc (fun op hc => by simp [withImpcC, withImpc, AT.add, TG.toAT, impcTG, hc])
        (fun _ _ _ _ _ _ hr => List.mem_append_left _ (List.mem_append_right _ hr))
        (fun op hc => by simp [withImpcC, AT.add, TG.toAT, colTG, hc])
        (fun _ _ _ _ _ _ hr => List.mem_append_right _ hr) hι
        (askHolds_of (hfoldA v (active_lt X.pf4 hv)) hS.1.2.2.2.1) (pfCells_of_rows hS.1 hv)
        (by rw [slotIn_π, slotπ_size]) (h v hv ι hι).2⟩

/-- The node's generator with both (the `askTG` edit: `… .add (impcTG …) |>.add (colTG …)`). -/
def askTGIC (π : ℕ) : TG := (askTGI π).add (colTG (XofT π) π (pvP π))

/-- (+) **The edit composes**: today's template with both has `askTGIC`'s fields. -/
theorem withImpcC_askT (π : ℕ) :
    (withImpcC askAq π).cov = (askTGIC π).cov ∧ (withImpcC askAq π).rows = (askTGIC π).rows :=
  ⟨rfl, rfl⟩

/-! ## Controls -/

/-- (+) **Provenance**: `[piField 0 3 5, input 0, piField 0 7 2]` has `piField` registers `0` and `2`;
(−) the `input`'s register `1` is none. -/
theorem provL_ctl : provL 0 [.piField 0 3 5, .input 0, .piField 0 7 2] = [(0, 0, 3, 5), (2, 0, 7, 2)] ∧
    provOf (provL 0 [.piField 0 3 5, .input 0, .piField 0 7 2]) 1 = none := ⟨rfl, rfl⟩

/-- (+) **A zero pin on bytes that are zero**: the flag of `assertZero 0` after `piField` of two zero
bytes is `true`; (−) on a nonzero byte it is `false` (what the pins must exclude). -/
theorem flag_ctl (impl : OpImpl) :
    flagOf impl .L32 ⟨0, 0, ⟨#[0, 0]⟩⟩ #[.b ⟨#[0, 0]⟩] (.assertZero 0 allK) = true ∧
      flagOf impl .L32 ⟨0, 0, ⟨#[0, 1]⟩⟩ #[.b ⟨#[0, 1]⟩] (.assertZero 0 allK) = false := by
  constructor <;> simp [flagOf, evalOp, rd, Val.isZero, allK] <;> decide

end N4s
end FR
