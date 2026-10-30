-- G6: this module also holds the former modules `FRNodeRun4CS`, `FRNodeRun4CD` (one section each, in import order).
import FRNodeRun4BT
import FRNodeRun4CB

section G6_FRNodeRun4CS

-- New for `flock-recursive` (track SIB): `ATImp` of the siblings' generator (`sibTG`), given that the proof's
-- sibling bytes are what its rows say (`SibOk`).

/-!
# The siblings' `ATImp`

A sibling read (`piDigest` in a queries phase's `fSibs` part, `sibAt`) is an import whose value is the
proof's 32 bytes there. `sibTG`'s rows say, per 16-byte half `c`, `sib_c = r_c + b·(l_c − r_c)` (`b` the
position bit's cell, `l`, `r` the node query's halves on arena₁) at the kinds whose depth is active, and
`sib_c = 0` at the others. **`SibOk`** says the proof's bytes are that (`FRNodeRun4CD.sibOk_of` proves it at
an active slot from the reader's format); **`atImp_sib`** is then the generator's `ATImp`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-- **The proof's sibling bytes are the rows'**: at a sibling read whose checks pass, half `c` of the 32 bytes
at `o` is `r_c + b·(l_c − r_c)` where kind `ι`'s depth is active, else `0`. -/
def SibOk (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (q : ByteArray) : Prop :=
  ∀ o n i p h k, sibAt o = some (n, i, p, h, k) → itemsT[k]? = some (.node i h) →
    1 + offT.getD k 0 + (Item.node i h).slen + 64 ≤ N4c.segB → kinds.all (sibPosOk T n i p h) = true →
    ∀ c < 2, F.ofBytes (bytesAt q (o + 16 * c) 16) =
      if h < (T.lvl ι i).sib then
        w (arC π (qElT k (.node i h) + 2 + c)) + w (bitC π (posCell i p h)) *
          (w (arC π (qElT k (.node i h) + c)) - w (arC π (qElT k (.node i h) + 2 + c)))
      else 0

theorem sibRow_ev {w : Asg} {b L R s : Lin}
    (h : (⟨b, subN L R, subN s R⟩ : Row).Holds w) : s.ev w = R.ev w + b.ev w * (L.ev w - R.ev w) := by
  simp only [Row.Holds, ev_subN] at h
  rw [h]; ring

/-- **`ATImp` of the siblings' generator** (read off an extension `Xa` agreeing with the compile's at the
sibling reads), given `SibOk`. -/
theorem atImp_sib {impl : OpImpl} {X Xa : Ext} {π : ℕ} {T : BTab} {κ : Kind} {inp : Input} {w : Asg}
    (hX : ∀ P cs op, sibCov op = true → stepOut Xa P cs op = stepOut X P cs op)
    (hS : SibOk T w π κ inp.π) : ATImp impl X (sibTG Xa π T).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  have hone := hc.1.1
  have hr := hc.2.2.2
  have hcv : sibCov op = true := hcov
  cases op <;> simp only [sibCov, reduceCtorEq, Bool.false_eq_true] at hcv
  rename_i f o
  obtain ⟨⟨n, i, p, h, kk⟩, hs⟩ := Option.isSome_iff_exists.1 hcv
  have hXe := hX P cs (.piDigest f o) (by simp [sibCov, hs])
  simp only [TG.toAT, sibTG, hs, hXe] at hr
  simp only [evalOp, Res.vals.injEq] at hev; obtain ⟨rfl, -⟩ := hev
  unfold sibRowsS at hr
  split at hr
  · rename_i i' h' s₀ s₁ hit hsl
    split_ifs at hr with hg
    · obtain ⟨rfl, rfl, hb, hpos⟩ := hg
      rw [hsl]
      refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      dsimp only at hr
      have hin : ¬ h' < (T.lvl κ i').sib → kinds.any (fun ι => decide ((T.lvl ι i').sib ≤ h')) = true :=
        fun hact => List.any_eq_true.2 ⟨κ, by cases κ <;> simp [kinds], by simpa using hact⟩
      have hS0 := hS _ _ _ _ _ _ hs hit hb hpos 0 (by norm_num)
      have hS1 := hS _ _ _ _ _ _ hs hit hb hpos 1 (by norm_num)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hS0 hS1
      have h0 : s₀.ev w = F.ofBytes (bytesAt inp.π (absOff f o) 16) := by
        rw [hS0]
        split_ifs with hact
        · rw [sibRow_ev (hr _ (List.mem_append_left _ List.mem_cons_self))]; simp [Lin.ev_cell]
        · rw [if_pos (hin hact)] at hr
          have := hr _ (List.mem_append_right _ List.mem_cons_self)
          simp only [Row.Holds, gateS_ev hc.1, Lin.ev_nil] at this
          rw [show decide ((T.lvl κ i').sib ≤ h') = true by simpa using hact] at this
          simpa [Circ.bitF] using this
      have h1 : s₁.ev w = F.ofBytes (bytesAt inp.π (absOff f o + 16) 16) := by
        rw [hS1]
        split_ifs with hact
        · rw [sibRow_ev (hr _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))]
          simp [Lin.ev_cell]
        · rw [if_pos (hin hact)] at hr
          have := hr _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
          simp only [Row.Holds, gateS_ev hc.1, Lin.ev_nil] at this
          rw [show decide ((T.lvl κ i').sib ≤ h') = true by simpa using hact] at this
          simpa [Circ.bitF] using this
      simp only [List.map_cons, List.map_nil, encV, dlo, dhi, digestAt_eq, h0, h1, bytesAt_lo, bytesAt_hi]
    · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)
  · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)

/-- **At a sibling read, `XofA`'s output is the compile's** (no template takes a `piDigest`). -/
theorem xofA_sib (π : ℕ) (P : Params) (cs : CS) (op : Op) (hop : sibCov op = true) :
    stepOut (XofA π) P cs op = stepOut (Xof π) P cs op := by
  cases op <;> simp only [sibCov, reduceCtorEq, Bool.false_eq_true] at hop <;>
    simp only [stepOut, XofA, Xof, XofC, tplExt4A, tplExt4, tplExt4S, Ext.orElse, tplExtKM, tplExtF, tplExt, extGetK,
      Option.orElse, Option.filter]

end N4s
end FR

end G6_FRNodeRun4CS

section G6_FRNodeRun4CD

-- New for `flock-recursive` (track SIB): `SibOk` at an active slot — the proof's sibling bytes are the reader's
-- format (`reassemble4`'s `fSibs` part) read with the selected kind's ladder (the kind tie).

/-!
# `SibOk` at a slot

At an active slot, the proof is `reassemble4` of the slot's trace (`slotπ_byte`). Its `fSibs` byte at a
sibling read is `sib4` of the node query at the trace's ladder `trM4` (`sib_bytes`: `reassemble4_byte`,
`ctb4_sibs`). Three facts make that the generator's row:

* **the kind tie** (`trM4_slot`): `trM4` reads the seed's byte 71, stream element 5's byte 0, which the
  pack rows tie to the selected index's constant (`kindRow_sel`), so `trM4` is the selected kind's `m`;
* **the position bit** (`posBit_of`): the position cell is bit `h` of the position (`PosBits` at the cell
  `sibPosOk` checked, the P2 answers `phAns` the trace's, `phAns_getD`);
* **the node query's halves** (`slot_qelemA`): arena₁'s cells are the query's 16-byte windows.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl X

/-! ## The sibling read's place -/

theorem sibAt_spec {o n i p h k : ℕ} (hs : sibAt o = some (n, i, p, h, k)) :
    ∃ sg ∈ pSegs, sg.f = fSibs ∧ sg.n = n ∧ sg.st ≤ o ∧ o < sg.st + sg.len ∧
      (phasesA.getD n ("", .seed)).2 = .queries i ∧ (o - sg.st) % 32 = 0 ∧ 0 < (seq4.lv i).sib ∧
      p = (o - sg.st) / 32 / (seq4.lv i).sib ∧ h = (o - sg.st) / 32 % (seq4.lv i).sib ∧
      k = phIxA.getD n 0 + (1 + (seq4.lv i).sib) * p + 1 + h := by
  unfold sibAt at hs
  split at hs
  · rename_i sg hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    simp only [sibSegs, List.mem_filter, beq_iff_eq] at hm
    split at hs
    · rename_i i' hq
      dsimp only at hs
      split_ifs at hs with hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨sg, hm.1, hm.2, rfl, hp.1, hp.2, hq, hd.1, hd.2, rfl, rfl, rfl⟩
    · cases hs
  · cases hs

/-- **A sibling read's bytes in the proof**: `sib4` of its node query at the trace's ladder. -/
theorem sib_bytes (tr : Trace) {o n i p h k : ℕ} (hs : sibAt o = some (n, i, p, h, k)) {t : ℕ} (ht : t < 32) :
    byteAt (reassemble4 seq4 tr) (o + t) =
      (sib4 seq4 (trM4 tr.toArray) i h (posOf4 seq4 (trM4 tr.toArray) i (phAns seq4 tr.toArray n) p)
        (tr.toArray.getD k (ByteArray.empty, 0)).1).getD t 0 ∧
      p < (seq4.lv i).t ∧ h < (seq4.lv i).sib ∧ 1 ≤ n ∧ n < (phasesOf seq4).length ∧
      ((phasesOf seq4).getD n ("", .seed)).2 = .queries i := by
  obtain ⟨sg, hm, hf, rfl, hst, hlt, hq, hd, hsib, rfl, rfl, rfl⟩ := sibAt_spec hs
  obtain ⟨hfl, hn, hst', hlen⟩ := mem_pSegs hm
  rw [hf] at hst' hlen hfl
  rw [phasesA_getD hn] at hq
  rw [hq] at hlen
  simp only [Sh.bytesToL, show fSibs ≠ fCols by decide, if_false, if_true] at hlen
  set S := seq4.lv i
  have hd32 : o - sg.st = 32 * ((o - sg.st) / 32) := by omega
  have hdl : (o - sg.st) / 32 < S.t * S.sib := by
    have : o - sg.st < S.t * S.sib * 32 := by omega
    omega
  have hp : (o - sg.st) / 32 / S.sib < S.t := by
    rw [Nat.div_lt_iff_lt_mul hsib]; exact hdl
  have hh : (o - sg.st) / 32 % S.sib < S.sib := Nat.mod_lt _ hsib
  have hdec : (o - sg.st) / 32 = (o - sg.st) / 32 / S.sib * S.sib + (o - sg.st) / 32 % S.sib := by
    rw [Nat.div_add_mod']
  have hn1 : 1 ≤ sg.n := by
    rcases Nat.eq_zero_or_pos sg.n with h0 | h0
    · exfalso
      obtain ⟨tl, htl⟩ := phasesOf_cons
      have hq' := hq
      simp only [h0, htl, List.getElem_cons_zero, reduceCtorEq] at hq'
    · exact h0
  refine ⟨?_, hp, hh, hn1, hn, by rw [List.getD_eq_getElem _ _ hn, hq]⟩
  have hj : o - sg.st + t < ((phasesOf seq4)[sg.n]).2.bytesToL seq4.lv fSibs := by
    rw [hq]; simp only [Sh.bytesToL, show fSibs ≠ fCols by decide, if_false, if_true]
    have : (o - sg.st) / 32 + 1 ≤ S.t * S.sib := hdl
    generalize S.t * S.sib = M at *
    omega
  rw [show o + t = fieldOffOf seq4 fSibs + phaseOffOf seq4 sg.n fSibs + (o - sg.st + t) by omega,
    reassemble4_byte seq4 tr hfl hn hj, hq]
  rw [show o - sg.st + t = ((o - sg.st) / 32 / S.sib * S.sib + (o - sg.st) / 32 % S.sib) * 32 + t by omega,
    ctb4_sibs (S := seq4) (trM4 tr.toArray) tr.toArray _ _ hp hh ht, phIxA_getD hn.le]

/-! ## `sib4`, the position answers, the position bits -/

theorem sib4_getD (S : Seq) (m i h j : ℕ) (q : ByteArray) {t : ℕ} (ht : t < 32) :
    (sib4 S m i h j q).getD t 0 =
      if h < (S.lvK m i).sib then (if j / 2 ^ h % 2 = 0 then byteAt q (40 + t) else byteAt q (8 + t)) else 0 := by
  rw [sib4]
  split_ifs with h1 h2
  · exact fitL_extract_getDj q 40 32 ht
  · exact fitL_extract_getDj q 8 32 ht
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos ht]; rfl

/-- `ansN` one phase further. -/
theorem ansN_succ (S : Seq) (a : Array (ByteArray × Digest)) : ∀ (shs : List Sh) (ix : ℕ) (ans : List Digest) (n : ℕ)
    (hn : n < shs.length), ansN S a ix ans shs (n + 1) =
      ansOf4 a (ix + ((shs.take n).map fun sh => (sh.itemsL S.lv).length).sum) (ansN S a ix ans shs n) shs[n]
  | [], _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | sh :: shs, ix, ans, 0, _ => by simp [ansN]
  | sh :: shs, ix, ans, n + 1, hn => by
    simp only [ansN, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [ansN_succ S a shs _ _ n (by simpa using hn), Nat.add_assoc]

/-- **The position answers a queries phase reads** are the P2 phase's just before it. -/
theorem phAns_getD (S : Seq) (a : Array (ByteArray × Digest)) {n sq i q : ℕ} (h1 : 1 ≤ n)
    (hn : n ≤ (phasesOf S).length) (hP : ((phasesOf S).getD (n - 1) ("", .seed)).2 = .squeezes sq (.pos i))
    (hq : q < sq) : (phAns S a n).getD q 0 = (a.getD (phIx S (n - 1) + q) (ByteArray.empty, 0)).2 := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn' : n < ((phasesOf S).map Prod.snd).length := by simpa using hn
  have hm : ((phasesOf S).map Prod.snd)[n] = .squeezes sq (.pos i) := by
    rw [List.getElem_map]; rw [List.getD_eq_getElem _ _ (by simpa using hn')] at hP; simpa using hP
  rw [phAns, ansN_succ S a _ 0 [] n hn', hm, Nat.zero_add, Nat.add_sub_cancel]
  simp only [ansOf4]
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, List.getElem_range, phIx]
  simp only [List.map_take, List.map_map]
  rfl

/-- **Bit `h` of a position** is bit `(p mod per)·logN + h` of its answer. -/
theorem posOf4_bit (S : Seq) (m i : ℕ) (ans : List Digest) (p : ℕ) {h : ℕ} (hh : h < (S.lvK m i).logN) :
    decide (posOf4 S m i ans p / 2 ^ h % 2 = 1) =
      (natLE (ans.getD (p / (S.lvK m i).per) 0)).testBit (p % (S.lvK m i).per * (S.lvK m i).logN + h) := by
  have := testBit_idxOfF (S.lvK m i).logN (ans.getD (p / (S.lvK m i).per) 0) (p % (S.lvK m i).per) h
  rw [idxOfF_eq, Nat.testBit_eq_decide_div_mod_eq] at this
  simp only [hh, decide_true, Bool.true_and] at this
  exact this

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) (N i : ℕ) (hd : N ≤ i → f i = d) :
    ((List.range N).map f).toArray.getD i d = f i := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  by_cases hi : i < N
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simpa using hi)]; exact (hd (by omega)).symm

/-- **A prototype table's ladder** is `seq4`'s at the kind's `m`. -/
theorem lvl_mkTab (ops : List Op) (G : Grp) (ι : Kind) (i : ℕ) : (mkTab ops G).lvl ι i = seq4.lvK (G ι).d.m i := by
  have hd : ∀ m, nLevels ≤ i → seq4.lvK m i = ⟨0, 1, 0, 0⟩ := fun m hi => by
    simp only [Seq.lvK, ladderOfR]
    rw [List.getD_eq_default _ _ (by simp [nLevels] at hi ⊢; omega)]
  have h1 : (mkTab ops G).lv.getD (kix ι) #[] =
      ((List.range nLevels).map fun i => seq4.lvK (G ι).d.m i).toArray := by
    cases ι <;> rfl
  simp only [BTab.lvl, h1]
  exact getD_range_map _ _ _ _ (hd _)

theorem mkTab_ans_lt {ops : List Op} {G : Grp} {k : ℕ} {v : ℕ × ℕ × ℕ}
    (h : (mkTab ops G).ans.getD k none = some v) : k < (itemsOf seq4).length := by
  have hs : (mkTab ops G).ans.size = (itemsOf seq4).length := by
    simp only [mkTab]
    generalize ansList.zipIdx = l
    suffices ∀ (acc : Array (Option (ℕ × ℕ × ℕ))), (l.foldl (fun (a : Array (Option (ℕ × ℕ × ℕ))) p =>
        a.set! p.1.1 (some (p.1.2.1, p.1.2.2, p.2))) acc).size = acc.size by rw [this]; simp
    induction l with
    | nil => intro acc; rfl
    | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp [Array.set!]
  by_contra hk
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
  cases h

/-! ## The kind tie -/

/-- Prototype `π`'s kind group. -/
def grpP (π : ℕ) : Grp := if π = 0 then nodeGrp else segGrp

theorem packB_grp (κ : NodeKind) (v : ℕ) : packB κ v = some (slotB0 κ v, grpP (protoOf κ v)) := by
  unfold packB slotB0 grpP protoOf; split_ifs <;> simp_all

theorem kConst_byte0 (π : ℕ) (ι : Kind) : (F.toBytes (kConst (grpP π) ι))[0] = (grpP π ι).byte := by
  unfold grpP; split_ifs
  · exact (kConst_byte ι).1
  · exact (kConst_byte ι).2

theorem byte_ne_zero (π : ℕ) (ι : Kind) : (grpP π ι).byte ≠ 0 := by
  unfold grpP; split_ifs <;> cases ι <;> decide

theorem ofByte_m (π : ℕ) (ι : Kind) :
    ((Snd.CKind.ofByte? (grpP π ι).byte).getD (.seg .L32)).m = (grpP π ι).d.m := by
  unfold grpP; split_ifs <;> cases ι <;> rfl

/-- **The kind tie**: at an active slot whose selector picks `ι`, the trace's ladder (`trM4`, the seed's
byte 71) is the selected kind's. -/
theorem trM4_slot {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ} {ι : Kind}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : N4c.Active4 (rd4 pf) κ w v)
    (hvs : v < κ.vslots) (hι : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) :
    trM4 (slotTr4 κ v w).toArray = (grpP (protoOf κ v) ι).d.m := by
  have hone := one_of_pubCells hS.2.2.2.2
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  have hk : 0 < (itemsOf seq4).length := by rw [hr]; simp
  obtain ⟨e, he⟩ : ∃ e, (slotTr4 κ v w)[0]? = some e := by
    rw [slotTr4_getElem?, hr]; exact ⟨_, rfl⟩
  have hb0 := slot_qbyte hv hk he (by rw [itAt_seed]; simp [itOff, Item.slen, Item.qlen, N4c.segB])
    (j := 71) (by rw [itAt_seed]; decide)
  obtain ⟨-, hrow, -⟩ := pins_of hS hvs (packB_grp κ v)
  have h5 := kindRow_sel hone hrow hι
  have hbyte : byteAt e.1 71 = (grpP (protoOf κ v) ι).byte := by
    rw [hb0]
    simp only [itOff, List.take_zero, List.map_nil, List.sum_nil]
    rw [← kConst_byte0, ← h5]
    rfl
  unfold trM4
  rw [tr_getD he]
  unfold byteAt at hbyte
  split at hbyte
  · rename_i hlt
    have hd : e.1.data[71]? = some (grpP (protoOf κ v) ι).byte := by
      rw [← hbyte]; exact (Array.getElem?_eq_getElem hlt)
    rw [hd, Option.bind_some, ofByte_m]
  · exact absurd hbyte.symm (byte_ne_zero _ _)

/-! ## `SibOk` -/

theorem ofBytes_zero16 : F.ofBytes (Vector.ofFn fun _ : Fin 16 => (0 : UInt8)) = 0 := by decide

theorem bitTabP_mkTab (π : ℕ) : bitTabP π = mkTab (protoProg π).ops (grpP π) := rfl

/-- **The position bit at an active depth** (the kind's ladder `m`): the cell `sibPosOk` checked holds bit `h`
of the position. -/
theorem posBit_eq {T : BTab} {w : Asg} {π : ℕ} {ι : Kind} {tr : Trace} (hPB : PosBits T w π ι tr)
    (hT : ∀ k v, T.ans.getD k none = some v → ∃ e, tr[k]? = some e) {m n i p h : ℕ} (hm : T.lvl ι i = seq4.lvK m i)
    (hpos : sibPosOk T n i p h ι = true) (hact : h < (T.lvl ι i).sib) (hn : n ≤ (phasesOf seq4).length) :
    w (bitC π (posCell i p h)) =
      Circ.bitF (decide (posOf4 seq4 m i (phAns seq4 tr.toArray n) p / 2 ^ h % 2 = 1)) := by
  unfold sibPosOk at hpos
  simp only [hact, if_true] at hpos
  split at hpos
  · rename_i sq i' hph
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpos
    obtain ⟨⟨hn1, rfl, hq⟩, hc⟩ := hpos
    have hn1' : n - 1 < (phasesOf seq4).length := by omega
    have hph' : ((phasesOf seq4).getD (n - 1) ("", .seed)).2 = .squeezes sq (.pos i') := by
      rw [List.getD_eq_getElem _ _ hn1', ← phasesA_getD hn1']; exact hph
    -- the answer's entry
    obtain ⟨v, hv⟩ : ∃ v, T.ans.getD (phIxA.getD (n - 1) 0 + p / (T.lvl ι i').per) none = some v := by
      revert hc; unfold BTab.ansCell; split
      · intro _; exact ⟨_, ‹_›⟩
      · intro hc; cases hc
    obtain ⟨e', he'⟩ := hT _ _ hv
    rw [hPB _ _ _ e' hc he']
    have hans := phAns_getD seq4 tr.toArray hn1 hn hph' hq
    rw [hm] at hans hact
    rw [posOf4_bit seq4 m i' _ p (by simp only [Level.sib] at hact; omega), hans,
      ← phIxA_getD hn1'.le, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    rw [hm] at he'
    rw [he', Option.getD_some, hm]
  · cases hpos

/-- **`SibOk` at an active slot**: the proof `q` is `reassemble4` of the slot's trace (byte by byte), the
position cells hold the answers' bits (`PosBits`). -/
theorem sibOk_of {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ} {ι : Kind} {q : ByteArray}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : N4c.Active4 (rd4 X.pf4) κ w v)
    (hvs : v < κ.vslots) (hι : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι)
    (hPB : PosBits (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι (slotTr4 κ v w))
    (hq : ∀ x, byteAt q x = byteAt (reassemble4 seq4 (slotTr4 κ v w)) x) :
    SibOk (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι q := by
  have hone := one_of_pubCells hS.2.2.2.2
  have hE := hS.2.2.2.1
  intro o n i p h k hs hit hb hpos c hc
  set π := protoOf κ v
  set tr := slotTr4 κ v w
  have hm : (bitTabP π).lvl ι i = seq4.lvK (trM4 tr.toArray) i := by
    rw [bitTabP_mkTab, lvl_mkTab, trM4_slot hS hv hvs hι]
  obtain ⟨-, -, -, hn1, hn, -⟩ := sib_bytes tr hs (t := 0) (by norm_num)
  obtain ⟨hk, hit'⟩ := itAt_of (by rw [← itemsT_get]; exact hit)
  obtain ⟨e, he⟩ : ∃ e, tr[k]? = some e := by rw [slotTr4_getElem?, itAt_eq hk]; exact ⟨_, rfl⟩
  have hbyte : ∀ r < 16, byteAt q (o + 16 * c + r) =
      if h < ((bitTabP π).lvl ι i).sib then
        (if posOf4 seq4 (trM4 tr.toArray) i (phAns seq4 tr.toArray n) p / 2 ^ h % 2 = 0
          then byteAt e.1 (40 + 16 * c + r) else byteAt e.1 (8 + 16 * c + r))
      else 0 := by
    intro r hr
    rw [hq, show o + 16 * c + r = o + (16 * c + r) by ring, (sib_bytes tr hs (t := 16 * c + r) (by omega)).1,
      tr_getD he, sib4_getD _ _ _ _ _ _ (by omega), hm]
    simp only [Nat.add_assoc]
  have hvec : bytesAt q (o + 16 * c) 16 = Vector.ofFn fun r : Fin 16 =>
      if h < ((bitTabP π).lvl ι i).sib then
        (if posOf4 seq4 (trM4 tr.toArray) i (phAns seq4 tr.toArray n) p / 2 ^ h % 2 = 0
          then byteAt e.1 (40 + 16 * c + r) else byteAt e.1 (8 + 16 * c + r))
      else 0 := by
    simp only [bytesAt]
    exact Vector.ext fun r hr => by simp only [Vector.getElem_ofFn]; exact hbyte r hr
  rw [hvec]
  have hb' : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB := by rw [← offT_get hk.le, hit']; exact hb
  have hal : (1 + itOff k + 8 + 8) % 16 = 0 := by have := qAl hk; rw [hit', itemTag_len] at this; simpa using this
  have hqE : qElT k (.node i h) = (1 + itOff k + 8 + 8) / 16 := by rw [qElT, offT_get hk.le, itemTag_len]; simp
  have hql : (itAt k).qlen = 72 := by rw [hit']; rfl
  have hqel : ∀ j, j + 16 ≤ 72 → (1 + itOff k + 8 + j) % 16 = 0 →
      F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (j + r)) =
        slotAsg κ v w (arC π ((1 + itOff k + 8 + j) / 16)) :=
    fun j hj hal' => slot_qelemA hone hE hv hvs hk he hb' (by rw [hql]; exact hj) hal'
  have hR : F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (40 + 16 * c + r)) =
      slotAsg κ v w (arC π (qElT k (.node i h) + 2 + c)) := by
    rw [hqel _ (by omega) (by omega), hqE]; congr 2; omega
  have hL : F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (8 + 16 * c + r)) =
      slotAsg κ v w (arC π (qElT k (.node i h) + c)) := by
    rw [hqel _ (by omega) (by omega), hqE]; congr 2; omega
  split_ifs with hact hp0 hp0
  · -- active, bit 0: the right half
    have hbit := posBit_eq hPB (fun k' v' hv' => ⟨_, by
        rw [slotTr4_getElem?, itAt_eq (mkTab_ans_lt hv')]; rfl⟩) hm
      (List.all_eq_true.1 hpos ι (by cases ι <;> simp [kinds])) hact hn.le
    rw [hbit, show decide (posOf4 seq4 (trM4 tr.toArray) i (phAns seq4 tr.toArray n) p / 2 ^ h % 2 = 1) = false by
      simp [hp0]]
    simp only [Circ.bitF]
    rw [← hR]; simp
  · -- active, bit 1: the left half
    have hbit := posBit_eq hPB (fun k' v' hv' => ⟨_, by
        rw [slotTr4_getElem?, itAt_eq (mkTab_ans_lt hv')]; rfl⟩) hm
      (List.all_eq_true.1 hpos ι (by cases ι <;> simp [kinds])) hact hn.le
    rw [hbit, show decide (posOf4 seq4 (trM4 tr.toArray) i (phAns seq4 tr.toArray n) p / 2 ^ h % 2 = 1) = true by
      simp only [decide_eq_true_eq]; omega]
    simp only [Circ.bitF]
    rw [← hL, ← hR]; simp only [↓reduceIte, mul_one, one_mul]; ring
  · exact ofBytes_zero16

end N4s
end FR

end G6_FRNodeRun4CD

section G6_FRNodeRun4CT

-- New for `flock-recursive` (track SIB): the node's template with the siblings and the closure folded
-- (`askTG`'s fold, `askFold_close`), and `Gap4.imp` / `Gaps4` from the closed residual `SlotRunC`.

/-!
# `Gaps4` from the closed residual

`FRNodeRows4.askTG` folds, after IMPC2's bits and statement reads, the siblings (`sibTG`, beside by `addE`)
and closes the whole (`TG.close`). As ask templates: **`withSib`**, **`withClose`**; **`askFold_close`** is the
fold (by `rfl`).

* **`gap4Imp_of_close`**: `Gap4.imp` from the replay, the fold, `StmtN4R` and, per active slot and
  selectable index, **`SlotRunC`** — the `felems` auxiliary cells and the imports of the replay ops neither
  `rt` nor the template covers (`impQP`). The siblings' `ATImp` is `atImp_sib` with `sibOk_of`; the closure's is `atImp_close`;
  `SlotRunB` comes from `SlotRunC` by `slotRunB_of_close`, then `SlotRunA` by `slotRunA_of_bits`.
* **`gap4Imp_rtC1dC`**, **`gaps4_of_runC`**: at the certificate's replay templates `rtC1d` (SEG-R2), over
  `withRep` (the template failing at the replay ops `rtC1d` does not cover, `TG.repF`);
* **`gaps4_of_runF`** (SEG-R2): `Gaps4` from `SlotRunF`, the `felems` cells alone (`impQP_repF`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-- **The node's template with the siblings** (beside, `addE`). -/
def withSib (Aq : ℕ → AT) (π : ℕ) : AT := (withBitsS Aq π).addE (sibTG (XofA π) π (bitTabP π)).toAT

/-- **The node's template failing at the replay ops `rtC1d π` does not cover** (SEG-R2, `TG.repF`). -/
def withRep (Aq : ℕ → AT) (π : ℕ) : AT := (withSib Aq π).repF (rtC1d π).cov

/-- **The node's template closed** (`askTG`'s, SIB; SEG-R2: over `withRep`). -/
def withClose (Aq : ℕ → AT) (π : ℕ) : AT := closeP (withRep Aq π) π

/-- **The fold** (`askTG` folds the siblings and the closure after IMPC2's classes). -/
theorem askFold_close {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withClose askAq) κ v arR2, p ∈ nodeIRows4 κ :=
  askFold (fun π _ => ⟨rfl, rfl⟩) hone hE

theorem sibCov_bitRowsB {T : BTab} {X : Ext} {π : ℕ} {P : Params} {c : CS} {pre : Option Op} {op : Op} {k : ℕ}
    {r : Row} (hr : r ∈ bitRowsB T X π P c pre op k) : sibCov op = false := by
  cases op <;> simp_all [bitRowsB, sibCov]

theorem addE_rows_left {A B : AT} {P : Params} {c : CS} {pre : Option Op} {op : Op} {k : ℕ} {r : Row}
    (hB : B.cov op = false) (hr : r ∈ A.rows P c pre op k) : r ∈ (A.addE B).rows P c pre op k := by
  simp only [AT.addE, hB, Bool.false_eq_true, ite_false]
  exact List.mem_append_left _ hr

/-- **`bitTGB`'s rows are the closed template's.** -/
theorem close_rowsB (π : ℕ) : ∀ c pre op k, ∀ r ∈ bitRowsB (bitTabP π) (XofA π) π (protoP π) c pre op k,
    r ∈ (withClose askAq π).rows (protoP π) c pre op k := by
  intro c pre op k r hr
  have hS := bitsS_rowsB π c pre op k r hr
  have hs := sibCov_bitRowsB hr
  have hs' : (sibTG (XofA π) π (bitTabP π)).cov op = false := hs
  have hE0 : r ∈ (withSib askAq π).rows (protoP π) c pre op k := addE_rows_left hs' hS
  have hnr : isRep op = false := by cases op <;> first | rfl | simp [bitRowsB] at hr
  have hE : r ∈ (withRep askAq π).rows (protoP π) c pre op k := by
    rw [withRep, repF_rows (by simp [hnr])]; exact hE0
  have hcov : closeCov op = false ∨ (withRep askAq π).cov op = true := by
    cases op with
    | tensorW j r' =>
      right
      simp only [withRep, AT.repF, withSib, AT.addE, withBitsS, withBitsB, AT.addD, TG.toAT, bitTGB, bitCovB,
        Bool.or_true, Bool.true_or]
    | askSeed _ => left; rfl
    | selectHalf _ _ _ => left; rfl
    | _ => simp [bitRowsB] at hr
  simp only [withClose, closeP, AT.close]
  split
  · rename_i hcc
    rcases hcov with h | h
    · rw [h] at hcc; cases hcc
    · split
      · first | exact hE | (rw [if_pos h]; exact hE)
      · first | exact List.mem_append_left _ hE | (rw [if_pos h]; exact List.mem_append_left _ hE)
  · exact List.mem_append_left _ hE

/-- **`Gap4.imp` from the closed residual**: from the replay (`RepOk`, its fold), the fold of `withClose`,
`StmtN4R` and, at every active slot and selectable index, `SlotRunC`. -/
theorem gap4Imp_of_close {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withClose askAq) κ v arR2, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunC (rt (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) := by
  have hone := one_of_pubCells hS.1.2.2.2.2
  have hE := hS.1.2.2.2.1
  refine gap4Imp_of_runS hT₀ hT hok (fun e tr => X.pfHdr_reassemble4 e tr)
    (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) hfoldR hfoldA hS.1 fun v hv ι hι => ?_
  have hvs := active_lt X.pf4 hv
  have hask := askHolds_of (hfoldA v hvs) hE
  have hpc := pfCells_of_rows hS.1 hv
  have hX := tplExt4A_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base (protoOf_le' κ v) ι)
    (protoLay (protoOf κ v)) (colA (protoOf κ v))
  have hrB := close_rowsB (protoOf κ v)
  have hg := seed_rows hrB hask
  have hB : ∀ c < arNb, slotAsg κ v w (bitC (protoOf κ v) c) = 0 ∨ slotAsg κ v w (bitC (protoOf κ v) c) = 1 :=
    fun c hc => bit_slot hone hE hvs hc
  have hpad := (wots_aggPad_of_rows X.pf4 hS.1).2
  have hSt := stmtBits_of_glob hι.1 hpc hB hg
  have hPB : PosBits (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι ((rd4 X.pf4).slotTr κ v w) :=
    posBits_of_glob hι (fun k v h => mkTab_ans h) hB hg fun k it e hit he => by
      rw [itemsT_get] at hit
      obtain ⟨hkn, rfl⟩ := itAt_of hit
      have ha0 : aElT k (itAt k) = ansE k := by rw [aElT, offT_get hkn.le]; rfl
      have hs := itOff_slen hkn
      have hal := ans_al hkn
      obtain ⟨h1, h2⟩ := slot_ans' hv hpad hkn he
      rw [ha0, arC, a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), arC,
        a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), h1, h2]
      exact ⟨rfl, rfl⟩
  have hSib : SibOk (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v).π :=
    sibOk_of hS.1 hv hvs hι hPB fun x => by
      have : (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v).π = (rd4 X.pf4).slotπ κ v w := by
        unfold N4c.slotIn; split <;> rfl
      rw [this, X.slotπ_byte]; rfl
  refine ⟨atOk_close (extFl_xof _) (fun P cs op => xofA_isNone _ P cs op)
      (atOk_repF (atOk_addE (atOk_addD (atOk_addD (atOk_add (atOk_add (atOk_add (atOk_askT _ hS.1 hv hι)
        (atImp_inp (inpCells_of_rows (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr)
          (fun e tr => X.pfHdr_reassemble4 e tr) hS.1 v hv ι hι)))
        (atImp_rsv_slot hS.2.1 hS.2.2 v ι _)) (atImp_impc (pfCells_of_rows hS.1 hv)))
        (atImp_bitB (xofA_imp _))) (atImp_bitS (fun P cs op hop => xofA_read _ P cs op hop) hSt))
        (atImp_sib (fun P cs op hop => xofA_sib _ P cs op hop) hSib))), ?_⟩
  refine slotRunA_of_bits (Xa := XofA (protoOf κ v)) (stepOut_len hX _)
    (fun c j r => xofA_aux _ _ c j r)
    (fun op hc => by
      simp [withClose, closeP, AT.close, withRep, AT.repF, withSib, withBitsS, withBitsB, withImpc, AT.addE,
        AT.addD, AT.add, TG.toAT, impcTG, hc])
    (fun P c pre a act k r hr => by
      have hcc : closeCov (.assertZero a act) = true := rfl
      simp only [withClose, closeP, AT.close, hcc, if_true, opImp, Bool.false_eq_true, if_false]
      refine List.mem_append_left _ ?_
      rw [if_pos (by simp [withRep, AT.repF, withSib, withBitsS, withBitsB, withImpc, AT.addE, AT.addD, AT.add,
        TG.toAT, impcTG, impcCov])]
      rw [withRep, repF_rows (by simp [isRep])]
      simp only [withSib, AT.addE, TG.toAT, sibTG, sibCov, Bool.false_eq_true, if_false]
      refine List.mem_append_left _ ?_
      simp only [withBitsS, withBitsB, AT.addD, TG.toAT, bitTGS, bitTGB, bitCovS, bitCovB, withImpc, AT.add,
        impcTG, pvP] at hr ⊢
      simp [hr])
    (fun op hc => by
      simp [withClose, closeP, AT.close, withRep, AT.repF, withSib, withBitsS, withBitsB, AT.addE, AT.addD,
        TG.toAT, bitTGB, hc])
    hrB hι hask hpc hSt hPB ?_
  exact slotRunB_of_close (stepOut_len hX _) hι.1 hask (h v hv ι hι)

/-- **`Gap4.imp` at the certificate's replay templates** (`rtC1d`, `implB`; SEG-R2: was `rtC1c`). -/
theorem gap4Imp_rtC1dC {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunC (rtC1d (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp Sub4.implB (fun _ => Sub4.implB) κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) :=
  gap4Imp_of_close implT_implB (fun _ => implT_implB) repOk_rtC1dB
    (repFold (one_of_pubCells hS.1.2.2.2.2) hS.1.2.2.2.1)
    (askFold_close (one_of_pubCells hS.1.2.2.2.2) hS.1.2.2.2.1) hS h

/-- **`Gaps4` from the closed residual `SlotRunC` at `rtC1d`**: what is left per active slot is the `felems`
auxiliary cells and the imports of the replay ops neither `rtC1d` nor the template covers (none:
`impQP_repF`; see `gaps4_of_runF`). -/
theorem gaps4_of_runC
    (h : ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
        SlotRunC (rtC1d (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    Sub4.Gaps4 :=
  fun vk κ w c₁ c₂ ch hS => gap4Imp_rtC1dC hS (h vk κ w c₁ c₂ ch hS)

/-- **`Gaps4` from the `felems` run facts alone** (SEG-R2): the replay ops' imports are gone (`rtC1d` replays
the five segment ops; any other replay op fails in the circuit, `TG.repF`), so per active slot and
selectable index what is left is `SlotRunF`: the `felems` auxiliary cells. -/
theorem gaps4_of_runF
    (h : ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
        SlotRunF (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    Sub4.Gaps4 :=
  gaps4_of_runC fun vk κ w c₁ c₂ ch hS v hv ι hι => slotRunC_of_F (h vk κ w c₁ c₂ ch hS v hv ι hι)

/-! ## Controls -/

namespace SibCtl

/-- (+) **`bitNxAll`**: a `bitOf` followed by a `selectHalf` on its result; (−) followed by another op, by a
`selectHalf` on another register, or last. -/
theorem bitNxAll_ctl : bitNxAll 5 [.bitOf 3 0, .selectHalf 5 1 2] = true ∧ bitNxAll 5 [.bitOf 3 0, .addF 1 2] = false ∧
    bitNxAll 5 [.bitOf 3 0, .selectHalf 4 1 2] = false ∧ bitNxAll 5 [.bitOf 3 0] = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- (+) **`closeCov`**: a proof read, an `input`, an assertion are the closure's; (−) an ask, a `bitOf`, a
replay op and an arithmetic op are not. -/
theorem closeCov_ctl : closeCov (.piDigest 17 0) = true ∧ closeCov (.input 0) = true ∧
    closeCov (.assertEq 0 1 fun _ => true) = true ∧ closeCov (.askSeed 0) = false ∧ closeCov (.bitOf 0 0) = false ∧
    closeCov (.shiftTarget 0 0 0 0) = false ∧ closeCov (.addF 0 1) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No template. -/
def X0 : Ext := fun _ _ _ => none
/-- A template taking every op. -/
def X1 : Ext := fun _ _ _ => some { slots := [] }
/-- Toy selector forms. -/
def P0 : Params := ⟨Lin.cell 0, fun _ => []⟩
/-- A table without a statement. -/
def T0 : BTab := ⟨#[], #[], #[], #[], 0, none⟩

/-- (+) **`impRows`**: an import no template takes fails (an `input`; a `piDigest`); (−) one a template may
take (`eqPt`) and takes does not. -/
theorem impRows_ctl : impRows X0 P0 (CS.init 0) (.input 0) = [failRT P0] ∧
    impRows X1 P0 (CS.init 0) (.piDigest 17 0) = [failRT P0] ∧ impRows X1 P0 (CS.init 0) (.eqPt 0 1) = [] := by
  refine ⟨rfl, rfl, rfl⟩

/-- (+) **`forRows`**: a foreign `assertBit` neither the zero pins nor the statement discharge fails; (−) an
`assertEq` off at every kind is not foreign. -/
theorem forRows_ctl : forRows X0 [] T0 P0 (CS.init 0) (.assertBit 0 fun _ => true) = [failRT P0] ∧
    forRows X0 [] T0 P0 (CS.init 0) (.assertEq 0 1 fun _ => false) = [] := by
  refine ⟨rfl, rfl⟩

/-- (+) **`TG.close`**: at an import its part does not cover, the failing row; (−) at one its part covers, the
part's rows; at the first ask with a `bitOf` not followed by its `selectHalf`, the failing row. -/
theorem close_ctl :
    (TG.none.close X0 [] T0 (bitNxAll 0 [])).rows P0 (CS.init 0) none (.input 0) 0 = [failRT P0] ∧
    ((inpTG X0 0).close X0 [] T0 (bitNxAll 0 [])).rows P0 (CS.init 0) none (.input 0) 0 = (inpTG X0 0).rows P0 (CS.init 0) none (.input 0) 0 ∧
    (TG.none.close X0 [] T0 (bitNxAll 0 [.bitOf 3 0])).rows P0 (CS.init 0) none (.askSeed 0) 0 = [failRT P0] ∧
    (TG.none.close X0 [] T0 (bitNxAll 0 [.bitOf 3 0, .selectHalf 0 1 2])).rows P0 (CS.init 0) none (.askSeed 0) 0 = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end SibCtl

end N4s
end FR

end G6_FRNodeRun4CT
