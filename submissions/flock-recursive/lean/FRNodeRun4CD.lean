-- New for `flock-recursive` (track SIB): `SibOk` at an active slot — the proof's sibling bytes are the reader's
-- format (`reassemble4`'s `fSibs` part) read with the selected kind's ladder (the kind tie).
import FRNodeRun4CS

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
