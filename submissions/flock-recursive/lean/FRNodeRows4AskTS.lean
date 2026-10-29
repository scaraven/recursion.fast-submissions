-- New for `flock-recursive` (PACK-4.4.1 §4.2; IMP-RESULT §5 item 2; track ASK-T): the ask generator is
-- sound — `ATAsk` for `askTGT` at every active slot of a node whose statement holds.
import FRNodeRows4AskTH

/-!
# Every ask's query is the trace's, and its answer slot represents the answer (`ATAsk`)

**`atAsk_T`**: at an active slot `v` of a node meeting `StmtN4`, with the slot's input (`inp.π` the
slot's proof, IMP's `input` cells holding `vk` and `c`), the generator `askTGT X π` (`π` the slot's
prototype) meets B3's `ATAsk` on the slot's trace. At ask `k` whose rows hold:

* the item check gives item `k` (`itemsT`) and its entry `e` (the reader's positional spec);
* the query is `e.1`, byte by byte (`q_bytes`): its tag from the pack rows' pins (`tag_byte`), each
  digest operand from its slot's cells, which the rows tie to arena₁, which is the slot's stream
  (`a1_slot`, `slot_qbyte'`; a node's halves are zero at an inactive depth, `dop_zero`), the seed's
  `vk`, `c` from the `input` cells, the byte operand from the previous `piField` at the item's
  source, which is `reassemble4`'s copy of the entry's own query bytes (`src_spec`);
* the answer slot's cells are arena₁'s answer elements, i.e. the entry's answer (`slot_ans'`).

Every item is covered, the last one too (`slot_byte'`, by `aggPad`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## Rows -/

section Rows
variable {w : Asg} {P : Params} {ι : Kind}

theorem failRT_false (hP : SelOk w P ι) : ¬ (failRT P).Holds w := by
  simp [failRT, Row.Holds, hP.1]

theorem chkR_ok (hP : SelOk w P ι) {b : Bool} (h : ∀ r ∈ chkR P b, r.Holds w) : b = true := by
  cases b
  · exact absurd (h _ (by simp [chkR])) (failRT_false hP)
  · rfl

theorem eqCR_val (hP : SelOk w P ι) {l : Lin} {c : ℕ} (h : (eqCR P l c).Holds w) : l.ev w = w c := by
  simp only [eqCR, Row.Holds, Lin.ev_sub, Lin.ev_cell, Lin.ev_nil, hP.1, one_mul] at h
  exact sub_eq_zero.mp h

theorem sel_self (hP : SelOk w P ι) : (P.sel ι).ev w = 1 := by rw [hP.2 ι, if_pos rfl]

theorem gated_val (hP : SelOk w P ι) {a c : Lin} (h : (⟨P.sel ι, a, c⟩ : Row).Holds w) : a.ev w = c.ev w := by
  simpa [Row.Holds, sel_self hP] using h

/-- **What a digest operand's rows give at the selected kind**: an active operand's slot is a digest
slot on arena₁'s two cells; an inactive one's elements are zero. -/
theorem dop_ok (hP : SelOk w P ι) {cs : CS} {r π E : ℕ} {act : KC Bool}
    (h : ∀ x ∈ dopRows P cs r π E act, x.Holds w) :
    (act ι = true → ∃ l₀ l₁, cs.slotK r ι = some (.d, [l₀, l₁]) ∧ l₀.ev w = w (arC π E) ∧
      l₁.ev w = w (arC π (E + 1))) ∧
    (act ι = false → w (arC π E) = 0 ∧ w (arC π (E + 1)) = 0) := by
  unfold dopRows at h
  split_ifs at h with hu
  · simp only [actAll, Bool.and_eq_true, decide_eq_true_eq] at hu
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hu
    have hact : act ι = true := by cases ι <;> assumption
    have hs : cs.slotK r ι = cs.slotK r .L32 := by cases ι <;> first | rfl | assumption
    refine ⟨fun _ => ?_, fun h' => absurd h' (by simp [hact])⟩
    rw [hs]
    split at h
    · next l₀ l₁ hl =>
      exact ⟨l₀, l₁, hl, eqCR_val hP (h _ (by simp)), eqCR_val hP (h _ (by simp))⟩
    · exact absurd (h _ (List.mem_singleton_self _)) (failRT_false hP)
  · have hk : ∀ x ∈ (if act ι then
        (match cs.slotK r ι with
        | some (.d, [l₀, l₁]) =>
          [⟨P.sel ι, l₀.sub (Lin.cell (arC π E)), []⟩, ⟨P.sel ι, l₁.sub (Lin.cell (arC π (E + 1))), []⟩]
        | _ => [⟨P.sel ι, P.one, []⟩])
        else [⟨P.sel ι, Lin.cell (arC π E), []⟩, ⟨P.sel ι, Lin.cell (arC π (E + 1)), []⟩] : List Row),
        x.Holds w :=
      fun x hx => h x (List.mem_flatMap.2 ⟨ι, by cases ι <;> simp [kinds], hx⟩)
    constructor
    · intro hact
      rw [if_pos hact] at hk
      split at hk
      · next l₀ l₁ hl =>
        refine ⟨l₀, l₁, hl, ?_, ?_⟩
        · have := gated_val hP (hk _ List.mem_cons_self)
          simp only [Lin.ev_sub, Lin.ev_cell, Lin.ev_nil] at this
          exact sub_eq_zero.mp this
        · have := gated_val hP (hk _ (List.mem_cons_of_mem _ List.mem_cons_self))
          simp only [Lin.ev_sub, Lin.ev_cell, Lin.ev_nil] at this
          exact sub_eq_zero.mp this
      · have := gated_val hP (hk _ (List.mem_singleton_self _))
        simp [hP.1] at this
    · intro hact
      rw [if_neg (by simp [hact])] at hk
      have h0 := gated_val hP (hk _ List.mem_cons_self)
      have h1 := gated_val hP (hk _ (List.mem_cons_of_mem _ List.mem_cons_self))
      simp only [Lin.ev_cell, Lin.ev_nil] at h0 h1
      exact ⟨h0, h1⟩

end Rows

/-- **A digest slot's register is a digest** with the slot's cells' halves. -/
theorem rd_dig {w : Asg} {cs : CS} {regs : Array Val} {κ : Kind} (hI : InvK w cs regs κ) {r : ℕ} {l₀ l₁ : Lin}
    (hs : cs.slotK r κ = some (.d, [l₀, l₁])) : ∃ x, rd regs r = .d x ∧ l₀.ev w = dlo x ∧ l₁.ev w = dhi x := by
  have h := rep_of_invK hI r
  rw [hs] at h
  obtain ⟨ht, he⟩ := h
  cases hv : rd regs r <;> rw [hv] at ht he <;> simp [tyOf] at ht
  rename_i x
  simp only [List.map_cons, List.map_nil, encV, List.cons.injEq, and_true] at he
  exact ⟨x, rfl, he.1, he.2⟩

/-! ## Bytes -/

theorem toBytes_dlo (x : Digest) {r : ℕ} (hr : r < 16) : (F.toBytes (dlo x))[r] = x[r] := by
  rw [dlo, F.toBytes_ofBytes, Vector.getElem_ofFn]

theorem toBytes_dhi (x : Digest) {r : ℕ} (hr : r < 16) : (F.toBytes (dhi x))[r] = x[16 + r] := by
  rw [dhi, F.toBytes_ofBytes, Vector.getElem_ofFn]

theorem flatMap_dig : ∀ (ds : List Digest) (d r : ℕ), d < ds.length → r < 32 →
    (ds.flatMap Vector.toList).getD (32 * d + r) 0 = (ds.getD d zeroD).toList.getD r 0
  | [], _, _, hd, _ => absurd hd (Nat.not_lt_zero _)
  | x :: ds, 0, r, _, hr => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by simpa using hr)]; rfl
  | x :: ds, d + 1, r, hd, hr => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by simp; omega), Vector.length_toList,
      show 32 * (d + 1) + r - 32 = 32 * d + r by omega, flatMap_dig ds d r (by simpa using hd) hr]; rfl

theorem flatMap_dig_len (ds : List Digest) : (ds.flatMap Vector.toList).length = 32 * ds.length := by
  induction ds with
  | nil => rfl
  | cons x ds ih => simp [List.flatMap_cons, ih]; ring

/-- **A query from its bytes**: the tag, the digests (32 bytes each), the message. -/
theorem q_bytes {e : ByteArray} (tag : List UInt8) (ds : List Digest) (msg : ByteArray)
    (hs : e.size = tag.length + 32 * ds.length + msg.size)
    (ht : ∀ j < tag.length, byteAt e j = tag.getD j 0)
    (hd : ∀ d < ds.length, ∀ r < 32, byteAt e (tag.length + 32 * d + r) = (ds.getD d zeroD).toList.getD r 0)
    (hm : ∀ j < msg.size, byteAt e (tag.length + 32 * ds.length + j) = byteAt msg j) :
    e = bytesOf (tag ++ ds.flatMap Vector.toList) ++ msg := by
  refine ByteArray.ext (Array.ext' ?_)
  have hl := flatMap_dig_len ds
  rw [ByteArray.data_append, Array.toList_append]
  show e.data.toList = (tag ++ ds.flatMap Vector.toList) ++ msg.data.toList
  have hsz : e.data.toList.length = e.size := by simp
  refine List.ext_getElem (by simp [hsz, hs, hl]; omega) fun j h₁ h₂ => ?_
  rw [← List.getD_eq_getElem _ 0 h₁, ← List.getD_eq_getElem _ 0 h₂, ← byteAt_toList]
  rw [hsz] at h₁
  by_cases h1 : j < tag.length
  · rw [List.append_assoc, List.getD_append _ _ _ _ h1, ht j h1]
  by_cases h2 : j < tag.length + 32 * ds.length
  · rw [List.getD_append _ _ _ _ (by simp [hl]; omega), List.getD_append_right _ _ _ _ (by omega),
      show j = tag.length + 32 * ((j - tag.length) / 32) + (j - tag.length) % 32 by omega,
      hd _ (by omega) _ (Nat.mod_lt _ (by norm_num)), Nat.add_assoc, Nat.add_sub_cancel_left,
      flatMap_dig ds _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
  · rw [List.getD_append_right _ _ _ _ (by simp [hl]; omega), List.length_append, hl,
      show j = tag.length + 32 * ds.length + (j - (tag.length + 32 * ds.length)) by omega,
      hm _ (by omega), byteAt_toList, Nat.add_sub_cancel_left]

theorem append_empty' (b : ByteArray) : b ++ ByteArray.empty = b :=
  ByteArray.ext (by simp)

/-! ## At a slot -/

section Slot
variable {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ}

theorem entry_size (hv : N4c.Active4 (rd4 pf4) κ w v) {k : ℕ} (hk : k < (itemsOf seq4).length)
    {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e) : e.1.size = (itAt k).qlen := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hs := itOff_slen hk
  have hL := slotStr_len hv
  simp only [Read.entryAt, ByteArray.size, List.size_toArray, List.length_take, List.length_drop]
  omega

/-- The trace entry by position. -/
theorem tr_getD {k : ℕ} {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e) :
    (slotTr4 κ v w).toArray.getD k (ByteArray.empty, 0) = e := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, he, Option.getD_some]

/-- **A digest operand's bytes in the entry**: if the H cells of the query's elements `2d`, `2d + 1`
past its first carry `x`'s halves, its bytes `T + 32 d …` are `x`'s. -/
theorem dig_entry (hv : N4c.Active4 (rd4 X.pf4) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 X.pf4) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    {d E : ℕ} (hd : (itemTag (itAt k)).length + 32 * d + 32 ≤ (itAt k).qlen)
    (hEq : (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 + 2 * d = E) {x : Digest}
    (h₀ : w (sCell (slotB0 κ v) E) = dlo x) (h₁ : w (sCell (slotB0 κ v) (E + 1)) = dhi x) :
    ∀ r < 32, byteAt e.1 ((itemTag (itAt k)).length + 32 * d + r) = x.toList.getD r 0 := by
  intro r hr
  have hal := qAl hk
  have hxr : x.toList.getD r 0 = x[r] := by rw [List.getD_eq_getElem _ 0 (by simp; omega)]; simp
  rw [slot_qbyte' hv hpad hk he (by omega), hxr]
  rcases Nat.lt_or_ge r 16 with h16 | h16
  · rw [toBytes_idx (b := dlo x) (by rw [← h₀]; congr 2; omega) (s := r) (by omega), toBytes_dlo x h16]
  · rw [toBytes_idx (b := dhi x) (by rw [← h₁]; congr 2; omega) (s := r - 16) (by omega),
      toBytes_dhi x (by omega)]
    congr 1; omega

/-- **The byte operand at item `k`'s source**: its size and its bytes, the entry's query bytes from
`qoffOf`. -/
theorem msg_spec {inp : Input} (hπ : inp.π = (rd4 X.pf4).slotπ κ v w) {k A len : ℕ}
    (hsrc : (srcOf seq4)[k]? = some (some (A, len))) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e) :
    (inp.π.extract A (A + len)).size = len ∧
      ∀ j < len, byteAt (inp.π.extract A (A + len)) j = byteAt e.1 (qoffOf (itAt k) + j) := by
  obtain ⟨-, -, hle, hby⟩ := src_spec hsrc
  have hsz : inp.π.size = piSizeOf seq4 := by
    rw [hπ]; show (slotPf X.pf4 κ v w).toArray.size = _; rw [List.size_toArray, slotPf, fitL_length]
  refine ⟨by rw [ByteArray.size_extract, hsz]; omega, fun j hj => ?_⟩
  rw [byteAt_extract _ _ _ hj, hπ, X.slotπ_byte, show X.pf4 = X.reassemble4 seq4 from rfl, hby _ j hj, tr_getD he]

theorem preOk_spec {cs : CS} {pre : Option Op} {m k : ℕ} (h : preOk cs pre m k = true) :
    ∃ f o len, pre = some (.piField f o len) ∧ m + 1 = cs.slots.size ∧ srcT[k]? = some (some (absOff f o, len)) := by
  unfold preOk at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, _, _, rfl, h⟩
  · simp at h

theorem dlo_zero : dlo zeroD = 0 := by decide
theorem dhi_zero : dhi zeroD = 0 := by decide

end Slot

/-! ## The generator is sound -/

/-- **`ATAsk` for the ask generator** at an active slot `v` of a node meeting `StmtN4`, on the slot's
trace, for an input whose proof is the slot's and whose `input` cells hold its `vk` and `c`. -/
theorem atAsk_T (Xe : Ext) (impl : OpImpl) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : N4c.Active4 (rd4 X.pf4) κ w v)
    {ι : Kind} {inp : Input} (hπ : inp.π = (rd4 X.pf4).slotπ κ v w)
    (hin : InpCells (slotAsg κ v w) (protoOf κ v) inp) :
    ATAsk impl Xe (askTGT Xe (protoOf κ v)).toAT ι inp (slotAsg κ v w) (slotTr4 κ v w) := by
  intro P cs pre op k regs q e hc hq he
  have hP := hc.1
  have hI := hc.2.1
  have hrows : ∀ r ∈ askRowsG Xe (protoOf κ v) P cs pre op k, r.Holds (slotAsg κ v w) := hc.2.2.2
  have hone := one_of_pubCells hS.2.2.2.2
  have hE := hS.2.2.2.1
  have hvs := active_lt X.pf4 hv
  have hpad := (wots_aggPad_of_rows X.pf4 hS).2
  have hA1 : ∀ E, 16 * E + 16 ≤ N4c.segB → slotAsg κ v w (arC (protoOf κ v) E) = w (sCell (slotB0 κ v) E) :=
    fun E hE' => a1_slot hone hE hvs (elem_arN hE')
  obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 (ask_item hq)
  unfold askRowsG at hrows
  rw [hit] at hrows
  dsimp only at hrows
  by_cases hk : itemsT[k]? = some it
  swap
  · rw [if_neg hk] at hrows; exact absurd (hrows _ (List.mem_singleton_self _)) (failRT_false hP)
  rw [if_pos hk] at hrows
  rw [itemsT_get] at hk
  obtain ⟨hkn, hia⟩ := itAt_of hk
  subst hia
  have hq0 : qElT k (itAt k) = (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 := by
    rw [qElT, offT_get hkn.le]
  have ha0 : aElT k (itAt k) = ansE k := by rw [aElT, offT_get hkn.le]; rfl
  have hbody := fun r h => hrows r (List.mem_append_left _ h)
  have hans := fun r h => hrows r (List.mem_append_right _ h)
  rw [ha0] at hans
  have hs := itOff_slen hkn
  have hal := qAl hkn
  refine ⟨?_, ?_⟩
  swap
  · unfold ansRowsT at hans
    split at hans
    · next l₀ l₁ hsl =>
      obtain ⟨h1, h2⟩ := slot_ans' hv hpad hkn he
      have hal' := ans_al hkn
      refine ans_of_cells hsl ?_ ?_
      · rw [eqCR_val hP (hans _ List.mem_cons_self), hA1 (ansE k) (by unfold ansE; omega), h1]
      · rw [eqCR_val hP (hans _ (List.mem_cons_of_mem _ List.mem_cons_self)), hA1 (ansE k + 1) (by unfold ansE; omega), h2]
    · exact absurd (hans _ (List.mem_singleton_self _)) (failRT_false hP)
  have hsz := entry_size hv hkn he
  have htag := fun j (hj : j < (itemTag (itAt k)).length) => tag_byte hS hv hvs hpad hkn he hj
  -- a digest operand of the rows at element `E` (active at `ι`) is a digest whose bytes are the entry's
  have hdop : ∀ {r d E : ℕ} {act : KC Bool}, (∀ x ∈ dopRows P cs r (protoOf κ v) E act, x.Holds (slotAsg κ v w)) →
      (itemTag (itAt k)).length + 32 * d + 32 ≤ (itAt k).qlen →
      (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 + 2 * d = E →
      (act ι = true → ∃ x, rd regs r = .d x ∧
        ∀ j < 32, byteAt e.1 ((itemTag (itAt k)).length + 32 * d + j) = x.toList.getD j 0) ∧
      (act ι = false → ∀ j < 32, byteAt e.1 ((itemTag (itAt k)).length + 32 * d + j) = zeroD.toList.getD j 0) := by
    intro r d E act hR hd hEq
    have hb : 16 * (E + 1) + 16 ≤ N4c.segB := by omega
    obtain ⟨hon, hoff⟩ := dop_ok hP hR
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · obtain ⟨l₀, l₁, hsl, h0, h1⟩ := hon ha
      obtain ⟨x, hx, hx0, hx1⟩ := rd_dig hI hsl
      refine ⟨x, hx, dig_entry hv hpad hkn he hd hEq ?_ ?_⟩
      · rw [← hA1 _ (by omega), ← h0, hx0]
      · rw [← hA1 _ hb, ← h1, hx1]
    · obtain ⟨z0, z1⟩ := hoff ha
      refine dig_entry hv hpad hkn he hd hEq ?_ ?_
      · rw [← hA1 _ (by omega), z0, dlo_zero]
      · rw [← hA1 _ hb, z1, dhi_zero]
  -- the byte operand at the item's source
  have hmsg : ∀ {m : ℕ}, preOk cs pre m k = true → ∃ msg : ByteArray, rd regs m = .b msg ∧
      msg.size + qoffOf (itAt k) = (itAt k).qlen ∧ ∀ j < msg.size, byteAt msg j = byteAt e.1 (qoffOf (itAt k) + j) := by
    intro m hp
    obtain ⟨f, o, len, rfl, hm, hsrc⟩ := preOk_spec hp
    rw [srcT_get] at hsrc
    obtain ⟨-, hql, -, -⟩ := src_spec hsrc
    obtain ⟨hz, hb⟩ := msg_spec hπ hsrc he
    exact ⟨_, rd_of_piField hc hm, by omega, fun j hj => hb j (by omega)⟩
  cases op with
  | askSeed h =>
    have hia : itAt k = .seed := by simpa [Op.item?] using hit.symm
    simp only [evalOp, Res.ask.injEq] at hq
    subst hq
    obtain ⟨msg, hm, hmz, hmb⟩ := hmsg (chkR_ok hP fun r hr => hbody r (List.mem_append_left _ hr))
    have hc4 : ∀ j < 4, slotAsg κ v w (arC (protoOf κ v) (qElT k (itAt k) + j)) =
        slotAsg κ v w (inCT (protoOf κ v) (j / 2) (j % 2)) := fun j hj =>
      by simpa using eqCR_val hP (hbody _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))
    obtain ⟨i0, i1, i2, i3⟩ := hin
    have hT : (itemTag (itAt k)).length = 7 := by rw [hia]; rfl
    have hql : (itAt k).qlen = 119 := by rw [hia]; rfl
    have hqo : qoffOf (itAt k) = 71 := by rw [hia]; rfl
    have hcell : ∀ j < 4, ∀ E, E = (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 + j →
        w (sCell (slotB0 κ v) E) = slotAsg κ v w (inCT (protoOf κ v) (j / 2) (j % 2)) := fun j hj E hE' => by
      rw [← hA1 E (by omega), hE', ← hq0, hc4 j hj]
    have hds : ∀ d < [inp.vk, inp.c].length, ∀ r < 32, byteAt e.1 ((itemTag (itAt k)).length + 32 * d + r) =
        ([inp.vk, inp.c].getD d zeroD).toList.getD r 0 := by
      intro d hd r hr
      simp only [List.length_cons, List.length_nil] at hd
      rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
      · exact dig_entry hv hpad hkn he (d := 0) (E := (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 + 0)
          (by omega) (by omega) ((hcell 0 (by norm_num) _ rfl).trans i0) ((hcell 1 (by norm_num) _ (by omega)).trans i1) r hr
      · exact dig_entry hv hpad hkn he (d := 1) (E := (1 + itOff k + 8 + (itemTag (itAt k)).length) / 16 + 2)
          (by omega) (by omega) ((hcell 2 (by norm_num) _ rfl).trans i2) ((hcell 3 (by norm_num) _ (by omega)).trans i3) r hr
    rw [hm]
    change e.1 = seedQ inp.vk inp.c msg
    rw [q_bytes (itemTag (itAt k)) [inp.vk, inp.c] msg (by rw [hsz, hT]; simp; omega) htag hds
      (fun j hj => by rw [hmb j hj, hqo, hT]; rfl), hia]
    simp [seedQ, itemTag, List.append_assoc]
  | askAbsorb st m len =>
    have hia : itAt k = .absorb len := by simpa [Op.item?] using hit.symm
    simp only [evalOp, Res.ask.injEq] at hq
    subst hq
    obtain ⟨msg, hm, hmz, hmb⟩ := hmsg (chkR_ok hP fun r hr => hbody r (List.mem_append_left _ hr))
    obtain ⟨x, hx, hxb⟩ := (hdop (d := 0) (fun r hr => hbody r (List.mem_append_right _ hr))
      (by rw [hia]; simp [Item.qlen, itemTag, tagAbs]) (by rw [hq0] <;> omega)).1 rfl
    rw [hx, hm]
    change e.1 = absorbQ x msg
    rw [hia] at hsz hmz hmb htag hxb
    rw [q_bytes (itemTag (.absorb len)) [x] msg (by rw [hsz]; simp [qoffOf, Item.qlen] at hmz ⊢; simp [itemTag, tagAbs]; omega)
      htag (fun d hd r hr => by simp at hd; subst hd; simpa using hxb r hr)
      (fun j hj => by rw [hmb j hj]; rfl)]
    simp [absorbQ, itemTag]
  | askSqueeze st =>
    have hia : itAt k = .squeeze := by simpa [Op.item?] using hit.symm
    simp only [evalOp, Res.ask.injEq] at hq
    subst hq
    obtain ⟨x, hx, hxb⟩ := (hdop (d := 0) hbody (by rw [hia]; simp [Item.qlen, itemTag, tagSqz])
      (by rw [hq0] <;> omega)).1 rfl
    rw [hx]
    change e.1 = squeezeQ x
    rw [hia] at hsz htag hxb
    rw [q_bytes (itemTag .squeeze) [x] ByteArray.empty (by rw [hsz]; simp [Item.qlen, itemTag, tagSqz])
      htag (fun d hd r hr => by simp at hd; subst hd; simpa using hxb r hr)
      (fun j hj => absurd hj (by simp)), append_empty']
    simp [squeezeQ, itemTag]
  | askNode i hh l r act =>
    have hia : itAt k = .node i hh := by simpa [Op.item?] using hit.symm
    simp only [evalOp, Res.ask.injEq] at hq
    subst hq
    have hl := hdop (d := 0) (fun x hx => hbody x (List.mem_append_left _ hx))
      (by rw [hia]; simp [Item.qlen, itemTag, tagNode]) (by rw [hq0] <;> omega)
    have hr := hdop (d := 1) (fun x hx => hbody x (List.mem_append_right _ hx))
      (by rw [hia]; simp [Item.qlen, itemTag, tagNode]) (by rw [hq0] <;> omega)
    rw [hia] at hsz htag hl hr
    have key : ∀ x y : Digest,
        (∀ j < 32, byteAt e.1 ((itemTag (.node i hh)).length + 32 * 0 + j) = x.toList.getD j 0) →
        (∀ j < 32, byteAt e.1 ((itemTag (.node i hh)).length + 32 * 1 + j) = y.toList.getD j 0) →
        e.1 = nodeQF i x y := by
      intro x y hxb hyb
      rw [nodeQF_eq, q_bytes (itemTag (.node i hh)) [x, y] ByteArray.empty
        (by rw [hsz]; simp [Item.qlen, itemTag, tagNode])
        htag (fun d hd j hj => by
          simp at hd
          rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
          · simpa using hxb j hj
          · simpa using hyb j hj)
        (fun j hj => absurd hj (by simp)), append_empty']
      simp [nodeQ, itemTag, List.append_assoc]
    cases ha : act ι
    · rw [if_neg (by simp [ha])]
      exact key _ _ (hl.2 ha) (hr.2 ha)
    · rw [if_pos rfl]
      obtain ⟨x, hx, hxb⟩ := hl.1 ha
      obtain ⟨y, hy, hyb⟩ := hr.1 ha
      rw [hx, hy]
      exact key _ _ hxb hyb
  | askCol i c =>
    have hia : itAt k = .col i := by simpa [Op.item?] using hit.symm
    simp only [evalOp, Res.ask.injEq] at hq
    subst hq
    obtain ⟨msg, hm, hmz, hmb⟩ := hmsg (chkR_ok hP hbody)
    rw [hm]
    change e.1 = colQ i msg
    rw [hia] at hsz hmz hmb htag
    rw [q_bytes (itemTag (.col i)) [] msg (by rw [hsz]; simp [qoffOf, Item.qlen] at hmz ⊢; simp [itemTag, tagCol]; omega)
      htag (fun d hd => absurd hd (by simp)) (fun j hj => by rw [hmb j hj]; rfl)]
    simp [colQ, itemTag]
  | _ => simp [Op.item?] at hit

end N4s
end FR
