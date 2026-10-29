-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 steps 2–4; stage S-H4, pass 6, items 1–2
-- composed, item 4's decode half).
import FRXDec4Levels
import FRXChain4
import FRXReadLv
import FRX4Ext

/-!
# The node branch's decode at a revision 4.1 node kind (`decF04`)

3.x's `FRXNode.decF0` at a node kind `κ`, on revision 4.4.1's format (`seq4`, `piSizeOf seq4 = 876,304`):

`idxIR4 memX4 pL4 ; readK4 0 ; chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR ; decLevels4 κ`

(the log index at `memX4`, level 0's word at `map4.l0.cb`, the Fiat–Shamir replay with the answers
at `ansB`, the five levels). The format enters through `pL4` (the log's tape word), `cw4 i` (the
caps' tape words), `tw4` (the final message's tape word) and `cbS4 i` (the P1 challenges in the
chain's answers); `fmt4_ctl` checks them against `fsMsgs4 seq4` at the cap and final absorbs.

**`decF04_sem`**: on a domain tape of a node proof of kind `κ` whose log has no state hit, if the
log's transcript `es` is the first-match chain the replay reads (`fmAns … = ansAt es`), its cap and
final absorbs are π's fields (`capPi4`, `finPi4`), and every level's word is close with
`A_c = jointAgree`, then level 0's rows `1 … 7` sit at `map4.l0.ob` as `msgOf κ L es 0 (1 + q)`.

**`kindNd4`** reads the node byte (tape word 5's low byte) into two flags for the branch's `ite`
(`N2`: `m = 31`; `N4`: `m = 32`; `N8` shares `N4`'s ladder, `decLevels4_m`).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

attribute [local irreducible] entryK storeM runPrims

/-! ## Main's format at `seq4` -/

/-- The log's tape word: `5 + ⌈|π|/8⌉` at `|π| = piSizeOf seq4`. -/
def pL4 : ℕ := 5 + (piSizeOf seq4 + 7) / 8

/-- Level `i`'s cap in π: the caps field, then the earlier levels' caps. -/
def capFO4 (i : ℕ) : ℕ := fieldOffOf seq4 fCaps + capOff4 seq4 i

/-- **Cap entry `e` of level `i`** as π carries it. -/
def capPi4 (i : ℕ) (π : Proof) (e : ℕ) : Digest := bytesAt π (capFO4 i + 32 * e) 32

/-- Its tape word. -/
def cw4 (i : ℕ) : ℕ := 5 + capFO4 i / 8

/-- The final message in π (field `fFinal`). -/
def finFO4 : ℕ := fieldOffOf seq4 fFinal

/-- **The final message's element `x`** as π carries it. -/
def finPi4 (π : Proof) (x : ℕ) : K := chK (bytesAt π (finFO4 + 32 * x) 32)

/-- Its tape word. -/
def tw4 : ℕ := 5 + finFO4 / 8

/-- (value) The format's numbers at `seq4`. -/
theorem fmt4_vals : pL4 = 109543 ∧ (List.range 5).map capFO4 = [20896, 37280, 45472, 53664, 61856] ∧
    finFO4 = 70048 ∧ piSizeOf seq4 = 876304 := by
  simp only [pL4, finFO4, piSizeOf_seq4]
  rw [seq4_eq]
  decide +kernel

/-- **Control: the offsets are the absorbs'**: `fsMsgs4 seq4` absorbs π's bytes
`capFO4 i … + 32·2^cap` at the cap positions (`T4.capPos i`) and `finFO4 … + 32·2^7` at the
final message (`phStart4 47`). -/
theorem fmt4_ctl : (List.range 5).map (fun i => (fsMsgs4 seq4).getD (T4.capPos i) none) =
      (List.range 5).map (fun i => some (capFO4 i, 32 * 2 ^ (seq4.lv i).cap)) ∧
    (fsMsgs4 seq4).getD (phStart4 47) none = some (finFO4, 32 * 2 ^ 7) := by
  simp only [T4.capPos, phStart4, fsStarts4_eq, capFO4, finFO4]
  rw [seq4_eq]
  decide +kernel

/-- The caps' depths do not depend on the kind. -/
theorem lv_cap4 (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    (Snd.CKind.lv κ i).cap = if i = 0 then 9 else 8 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> rfl

/-! ## The tape at the format's fields -/

section Tape

variable (c : Digest) (π : Proof) (L : Log)

/-- **The tape at a cap entry** of level `i ≤ 4` at `seq4`'s offsets. -/
theorem tape_cap4 (hps : π.size = piSizeOf seq4) {i e m : ℕ} (hi : i < 5)
    (he : e < 2 ^ (if i = 0 then 9 else 8)) (hm : m < 4) :
    (tp c π L).getD (cw4 i + 4 * e + m) 0 = (packBytes (capPi4 i π e).toList).getD m 0 := by
  obtain ⟨-, hv, -, hs⟩ := fmt4_vals
  rw [tp, getD_toArray, cw4, capPi4]
  have e0 : capFO4 i % 8 = 0 ∧ capFO4 i + 32 * 2 ^ (if i = 0 then 9 else 8) ≤ 70048 := by
    simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.cons.injEq] at hv
    interval_cases i <;> simp_all
  have hp : (if i = 0 then 9 else 8) ≤ 9 := by split_ifs <;> omega
  have hp2 : 2 ^ (if i = 0 then 9 else 8) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hp
  exact tape_capL c π L e0.1 (by rw [hps, hs]; omega) hm

/-- **The tape at the final message**: the two tape pairs of element `x < 128` are `finPi4`. -/
theorem tapeF_fin4 (hps : π.size = piSizeOf seq4) {x : ℕ} (hx : x < 128) :
    (⟨tapeF (tp c π L) (tw4 + 4 * x), tapeF (tp c π L) (tw4 + 4 * x + 2)⟩ : K) = finPi4 π x := by
  obtain ⟨-, -, hf, hs⟩ := fmt4_vals
  have T : ∀ m < 4, (tp c π L).getD (tw4 + 4 * x + m) 0 =
      (packBytes (bytesAt π (finFO4 + 32 * x) 32).toList).getD m 0 := fun m hm => by
    rw [tp, getD_toArray]
    exact tape_capL c π L (off := finFO4) (by rw [hf]) (by rw [hps, hs, hf]; omega) hm
  rw [finPi4, chK_words, tapeF, tapeF, ← T 0 (by norm_num), ← T 1 (by norm_num),
    ← T 2 (by norm_num), ← T 3 (by norm_num)]
  rfl

end Tape

/-! ## The kind dispatch -/

/-- The flag `N2`. -/ def rF2 : ℕ := 246
/-- The flag `N4`. -/ def rF4 : ℕ := 247

/-- **The node byte's flags**: `rF2 := (byte = N2)`, `rF4 := (byte = N4)` (tape word 5's low byte). -/
def kindNd4 : XIR :=
  .seq (readAt rB0 5) (.blk (X4.normPs ++ X4.eqPs rF2 0x4D ++ X4.eqPs rF4 0x4E))

theorem wf_kindNd4 : WF kindNd4 := by
  simp +decide only [kindNd4, readAt, X4.normPs, X4.eqPs, WF, Prim.dst, rA, rB0, rF2, rF4, rK,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

theorem lo_kindNd4 : Lo kindNd4 := by
  simp +decide only [kindNd4, readAt, X4.normPs, X4.eqPs, Lo, Prim.dst, rA, rB0, rF2, rF4, rK, regs,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

/-- **The node byte's flags** on a nonempty proof: `rF2` is `1` iff the first byte is `N2`'s,
`rF4` iff it is `N4`'s; the heap and the output are kept. -/
theorem kindNd4_sem (c : Digest) (π : Proof) (L : Log) (hπ : 0 < π.size) (s : St) (hM : Inv s.M) :
    rd (semXIR (tp c π L) kindNd4 s).M rF2 = (if byteAt π 0 = NodeKind.N2.byte then 1 else 0) ∧
    rd (semXIR (tp c π L) kindNd4 s).M rF4 = (if byteAt π 0 = NodeKind.N4.byte then 1 else 0) ∧
    (∀ y, regs ≤ y → rd (semXIR (tp c π L) kindNd4 s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) kindNd4 s).M ∧ (semXIR (tp c π L) kindNd4 s).o = s.o ∧
    (semXIR (tp c π L) kindNd4 s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have r5 := rd_readAt (tp c π L) s hM (d := rB0) (pos := 5) (by decide) (by norm_num)
  have hM1 := inv_sem (tp c π L) (P := readAt rB0 5) (by simp +decide [readAt, WF, Prim.dst, rA, rB0]) hM
  have z1 := size_sem (tp c π L) (readAt rB0 5) s
  have o1 : (semXIR (tp c π L) (readAt rB0 5) s).o = s.o := by simp [readAt, semXIR]
  have b2 := X4.bOf_tape c π L hπ 0x4D (by decide)
  have b4 := X4.bOf_tape c π L hπ 0x4E (by decide)
  have fr := hframe (tp c π L) kindNd4 s lo_kindNd4
  have e2 : ((byteAt π 0).toNat = (0x4D : Word).toNat) ↔ byteAt π 0 = NodeKind.N2.byte := by
    rw [show NodeKind.N2.byte = 0x4D from rfl, ← UInt8.toNat_inj]; rfl
  have e4 : ((byteAt π 0).toNat = (0x4E : Word).toNat) ↔ byteAt π 0 = NodeKind.N4.byte := by
    rw [show NodeKind.N4.byte = 0x4E from rfl, ← UInt8.toNat_inj]; rfl
  rw [kindNd4, semXIR_seq]
  rw [kindNd4, semXIR_seq] at fr
  generalize semXIR (tp c π L) (readAt rB0 5) s = s1 at r5 hM1 z1 o1 fr
  have hs1 : 256 ≤ s1.M.size := by rw [z1]; omega
  refine ⟨?_, ?_, ?_, inv_sem _ (by simp +decide only [X4.normPs, X4.eqPs, WF, Prim.dst, rB0, rF2, rF4,
    rK, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]) hM1, o1, by rw [size_sem, z1]⟩
  · rw [X4.semXIR_blk4]
    simp only [X4.runPrims_append]
    simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
      [rd_runPrims_of_not_writes, X4.rd_eqPs, X4.rd_normPs]
    rw [r5]
    have := b2; simp only [X4.bOf, tp] at this ⊢
    rw [this]; exact if_congr e2 rfl rfl
  · rw [X4.semXIR_blk4]
    simp only [X4.runPrims_append]
    rw [X4.rd_eqPs _ _ (by decide) (by decide) (by simp only [size_runPrims]; omega)]
    simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
      [rd_runPrims_of_not_writes, X4.rd_normPs]
    rw [r5]
    have := b4; simp only [X4.bOf, tp] at this ⊢
    rw [this]; exact if_congr e4 rfl rfl
  · exact fr

/-- The branch of a node kind: `N2`'s, `N4`'s or `N8`'s program. -/
def pickNd (κ : NodeKind) (P2 P4 P8 : XIR) : XIR :=
  match κ with
  | .N2 => P2
  | .N4 => P4
  | .N8 => P8

/-- **The dispatch on the node byte**. -/
def ndK4 (P2 P4 P8 : XIR) : XIR := .seq kindNd4 (.ite rF2 P2 (.ite rF4 P4 P8))

/-- On a node proof of kind `κ`, the dispatch runs `κ`'s branch after the flags. -/
theorem ndK4_sem (c : Digest) (π : Proof) (L : Log) {κ : NodeKind} (hb : byteAt π 0 = κ.byte)
    (hπ : 0 < π.size) (P2 P4 P8 : XIR) (s : St) (hM : Inv s.M) :
    semXIR (tp c π L) (ndK4 P2 P4 P8) s = semXIR (tp c π L) (pickNd κ P2 P4 P8) (semXIR (tp c π L) kindNd4 s) := by
  obtain ⟨f2, f4, -⟩ := kindNd4_sem c π L hπ s hM
  rw [ndK4, semXIR_seq]
  generalize semXIR (tp c π L) kindNd4 s = s1 at f2 f4
  have h42 : NodeKind.N4.byte ≠ NodeKind.N2.byte := by decide
  have h82 : NodeKind.N8.byte ≠ NodeKind.N2.byte := by decide
  have h84 : NodeKind.N8.byte ≠ NodeKind.N4.byte := by decide
  have h24 : NodeKind.N2.byte ≠ NodeKind.N4.byte := by decide
  have o1 : (1 : Word) ≠ 0 := by decide
  cases κ <;> simp only [semXIR, f2, f4, hb, pickNd, if_true, if_false, h42, h82, h84, h24, o1,
    if_pos, if_neg, not_false_eq_true]

/-! ## The decode at a node kind -/

/-- **The decode at node kind `κ`**: the index, level 0's read, the chain, the five levels. -/
def decF04 (κ : NodeKind) : XIR :=
  .seq (idxIR4 memX4 pL4) (.seq (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128)
    (.seq (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) (decLevels4 (.node κ) pL4 cw4 cbS4 tw4)))

/-- **The decode at a node kind leaves `f⁽⁰⁾`'s rows `1 … 7`** (BLUEPRINT §6.2 steps 2–4; 3.x's
`decF0_sem`): on a domain tape of a proof of `piSizeOf seq4` bytes whose log has no state hit, if
the log's transcript `es` is the first-match chain the replay reads, its cap absorbs are π's caps
(`capPi4`), its final absorb is π's final field (`finPi4`), and every level's word is close with
`A_c = jointAgree`, then after `decF04 κ` the heap at `map4.l0.ob + 2^(mLog 0 + 1) q + 2x` holds,
as an `F` value, coefficient `x` of row `1 + q` of `f⁽⁰⁾` (`msgOf κ L es 0`). -/
theorem decF04_sem (κ : NodeKind) (c : Digest) (π : Proof) (L : Log) (hD : Dom4 pL4 c π L)
    (hps : π.size = piSizeOf seq4) (hS : ¬ StateHit L) (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep4, fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap : ∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, T4.capDig es i e = capPi4 i π e)
    (hfin : ∀ x < 2 ^ T4.mLog (.node κ) 4, T4.finalAt es x = finPi4 π x)
    (hfar : ∀ i < 5, ¬ T4.farL (.node κ) L es i)
    (hA : ∀ i < 5, T4.consSet (.node κ) L es i =
      jointAgree (T4.wordK (.node κ) L es i) (T4.decodeL (.node κ) L es i))
    (s : St) (hM : Inv s.M) (hsz : memX4 + L.length + L.length ≤ s.M.size) :
    ∀ q < 7, ∀ x < 2 ^ T4.mLog (.node κ) 0,
      algebraMap F K (rdF (semXIR (tp c π L) (decF04 κ) s).M
        (map4.l0.ob + 2 * 2 ^ T4.mLog (.node κ) 0 * q + 2 * x)) = T4.msgOf (.node κ) L es 0 (1 + q) x := by
  set I := tp c π L
  obtain ⟨hpL, hcv, hfv, hsv⟩ := fmt4_vals
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have hps' : π.size = 876304 := hps.trans hsv
  have hpL60 : pL4 ≤ 2 ^ 60 := by rw [hpL]; norm_num
  have hb : regs ≤ memX4 := by simp only [regs]; omega
  have hb2 : memX4 ≤ 2 ^ 60 := by omega
  -- the tape at the caps
  have hcapT : ∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, ∀ m < 4,
      I.getD (cw4 i + 4 * e + m) 0 = (packBytes (T4.capDig es i e).toList).getD m 0 :=
    fun i hi e he m hm => by
      rw [hcap i hi e he]
      exact tape_cap4 c π L hps hi (by rw [← lv_cap4 (.node κ) hi]; exact he) hm
  have hcw : ∀ i < 5, cw4 i + 4 * 2 ^ (Snd.CKind.lv (.node κ) i).cap < 2 ^ 62 := fun i hi => by
    rw [lv_cap4 (.node κ) hi]
    simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.cons.injEq] at hcv
    simp only [cw4]
    interval_cases i <;> simp_all
  -- the index
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hb hb2 hpL60 c π L hD.hs hD.hq hD.ht s hM hsz
  have hM1 : Inv (semXIR I (idxIR4 memX4 pL4) s).M := inv_sem _ (wf_idxIR4 memX4 pL4) hM
  have z1 := size_sem I (idxIR4 memX4 pL4) s
  rw [decF04, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (idxIR4 memX4 pL4) s = s1 at r1 r2 r3 hM1 z1
  have hX : Sorted4 pL4 I L (fun a => rd s1.M (memX4 + a)) := ⟨r1, r2, r3⟩
  have hsz1 : memX4 ≤ s1.M.size := by rw [z1]; omega
  -- level 0's read
  obtain ⟨w1, w2, w3, hM2⟩ := readK4_sem hpL60 hD hX s1 hM1 (fun _ _ => rfl) hsz1 (κ := .node κ)
    (es := es) (i := 0) (cw := cw4 0) (sb := map4.l0.cb) (nw := 128) (by norm_num) (hcw 0 (by norm_num))
    (hcapT 0 (by norm_num)) (by rw [(lv04_nums κ).2.2.1]) (by norm_num)
    (by have := (lv04_nums κ).1; omega) (by simp only [regs]; omega)
  have z2 := size_sem I (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) s1
  generalize semXIR I (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) s1 = s2 at w1 w2 w3 hM2 z2
  have hsz2 : memX4 ≤ s2.M.size := z2 ▸ hsz1
  -- the chain
  obtain ⟨ch1, ch2⟩ := chain_dec4 seq4 (N := nRep4) (by decide) c π L hD.hs (by omega) (by omega)
    (by rw [hps]; exact fsMsgs4_aligned) hD.hq hD.ht hS st₀ s2 hM2 (by simp only [chEnd]; omega)
  have hM3 : Inv (semXIR I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2).M := inv_sem _
    (wf_chainIR pL4 nRep4 _ (wf_sdList _) (noWrite_seedIR (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))) hM2
  have z3 := size_sem I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2
  generalize semXIR I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2 = s3 at ch1 ch2 hM3 z3
  have kc : ∀ y, chEnd ≤ y → rd s3.M y = rd s2.M y := fun y hy =>
    ch2 y (by simp only [regs, chEnd] at hy ⊢; omega) (.inr hy)
  have hXs3 : ∀ a < L.length, rd s3.M (memX4 + a) = rd s1.M (memX4 + a) := fun a ha =>
    (kc _ (by simp only [chEnd]; omega)).trans (w2 a ha)
  have hW3 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s3.M (map4.l0.cb + 128 * j + 2 * r) = T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← w1 j hj r]
    exact rdF_eq (kc _ (by simp only [chEnd]; omega)) (kc _ (by simp only [chEnd]; omega))
  have hS3 : ∀ i < 5, ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s3.M (cbS4 i + 8 * v) = T4.sAt es i v := by
    intro i hi
    refine sAt4_words fun v hv m hm => ?_
    have hl : (Snd.CKind.lv (.node κ) i).ell ≤ (if i = 0 then 6 else 4) := by
      rcases κ with _ | _ | _ <;> interval_cases i <;> decide
    have hp := (cbS4_bounds hi hl).2.2
    exact ch1 _ (by omega) _ (hfm _ (by omega)) m hm
  -- the five levels
  have hfinT : ∀ x < 2 ^ T4.mLog (.node κ) 4,
      T4.finalAt es x = ⟨tapeF I (tw4 + 4 * x), tapeF I (tw4 + 4 * x + 2)⟩ := fun x hx => by
    have : 2 ^ T4.mLog (.node κ) 4 ≤ 2 ^ 7 := (msg4_four_params (.node κ)).2.2
    rw [hfin x hx, tapeF_fin4 c π L hps (by omega)]
  exact (decLevels4_sem hpL60 hD hX s3 hM3 (z3 ▸ hsz2) hXs3 hW3
    (fun i hi1 hi => hcw i (by omega)) (fun i hi1 hi => hcapT i (by omega))
    (fun i hi => by
      have hl : (Snd.CKind.lv (.node κ) i).ell ≤ (if i = 0 then 6 else 4) := by
        rcases κ with _ | _ | _ <;> interval_cases i <;> decide
      obtain ⟨b1, b2, -⟩ := cbS4_bounds hi hl
      exact ⟨by omega, by simp only [chEnd] at b2; omega⟩)
    hS3 hfinT (by simp only [tw4]; omega) hfar hA).1

/-! ## Well formed, loop bounds, cost, output, size -/

theorem wf_seedIR4 : WF seedIR ∧ ¬ Writes seedIR rCC ∧ ¬ Writes seedIR rCn5 :=
  ⟨wf_sdList _, noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem wf_decF04 (κ : NodeKind) : WF (decF04 κ) :=
  ⟨wf_idxIR4 memX4 pL4, wf_readK4 .., wf_chainIR pL4 nRep4 _ wf_seedIR4.1 wf_seedIR4.2.1,
    wf_decLevels4 ..⟩

theorem outs_decF04 (κ : NodeKind) (t : ℕ) : outs (decF04 κ) t = 0 := by
  rw [decF04, outs, outs, outs, outs_idxIR4, outs_readK4, outs_decLevels4,
    outs_chainIR pL4 nRep4 t _ (sd := seedIR) (outs_sdList t _)]

/-- **The decode's loop bounds** on every domain tape of a proof of `piSizeOf seq4` bytes: the
index and the chain count at most `|L| ≤ t/5` entries and the log's words; the rest has no tape
loop. -/
theorem safe_decF04 (κ : NodeKind) (c : Digest) (π : Proof) (L : Log) (hps : π.size = piSizeOf seq4)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (decF04 κ) := by
  have hs : 5 + (π.size + 7) / 8 = pL4 := by rw [hps]; rfl
  have hpL : pL4 = 109543 := fmt4_vals.1
  exact .seq (safe_idxIR4 memX4 pL4 (by omega) (tape_count_le4 c π L hs ht))
    (.seq (safe_of_noLoopT (noLoopT_readK4 ..))
      (.seq (safe_chainIR c π L hs hq ht nRep4 _ (noLoopT_sdList _) wf_seedIR4.1 wf_seedIR4.2.2)
        (safe_of_noLoopT (noLoopT_decLevels4 ..))))

/-- The decode's cost: the index, level 0's read, the chain, the five levels. -/
theorem cost_decF04_eq (κ : NodeKind) (t : ℕ) : cost (decF04 κ) t = (2592 + t / 5 * 11871) +
    cost (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) t +
    (34 + 9 * (4 * (nRep4 + 1)) + cost seedIR t + t / 5 * 24 + t * 179) +
    cost (decLevels4 (.node κ) pL4 cw4 cbS4 tw4) t + 3 := by
  rw [decF04, cost, cost, cost, cost_idxIR4, cost_chainIR, chTab4_length]
  ring

/-- **The decode's cost** at each node kind: `≤ 27,118,215,163,902 + 2,558 t` at `N2`
(`m = 31`) and `≤ 108,136,600,478,701 + 2,558 t` at `N4`, `N8` (`m = 32`): the five levels
(`cost_decLevels4`), level 0's read (`≤ 85,731,573,774`, `m = 32`'s), and `19,457` for the
index's and the chain's constants, the seed block and the sequencing. -/
theorem cost_le_decF04 (t : ℕ) :
    cost (decF04 .N2) t ≤ 27032483570671 + 85731573774 + 19457 + 2558 * t ∧
    cost (decF04 .N4) t ≤ 108050868885470 + 85731573774 + 19457 + 2558 * t ∧
    cost (decF04 .N8) t ≤ 108050868885470 + 85731573774 + 19457 + 2558 * t := by
  have hs := cost_seedIR t
  obtain ⟨d2, d4, d8⟩ := cost_decLevels4 pL4 cw4 cbS4 tw4 t
  have r : ∀ κ : NodeKind, cost (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) t ≤ 85731573774 := by
    intro κ
    rw [cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num)]
    cases κ <;> decide
  have h5 : t / 5 * 11871 + t / 5 * 24 ≤ 2379 * t := by omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [cost_decF04_eq] <;>
    [(rw [d2]; have := r .N2); (rw [d4]; have := r .N4); (rw [d8]; have := r .N8)] <;>
    simp only [nRep4] at * <;> omega

/-! ## Controls -/

/-- (−) **The cap offsets use each level's cap depth**: level 1's cap starts `32·2^9` bytes after
level 0's (whose cap has `2^9` entries), not `32·2^8`. -/
theorem capFO4_ctl : capFO4 1 = capFO4 0 + 32 * 2 ^ 9 ∧ capFO4 1 ≠ capFO4 0 + 32 * 2 ^ 8 := by
  have h := fmt4_vals.2.1
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq] at h
  omega

/-- A toy proof whose first byte is `b`. -/
def toyB (b : UInt8) : Proof := ⟨#[b]⟩

/-- (+/−) **The dispatch reads the node byte**: on `N2`'s byte `rF2` is set and `rF4` is not; on
`N4`'s byte the reverse; (+) `pickNd` runs the kind's branch. -/
theorem kindNd4_ctl (c : Digest) (L : Log) (s : St) (hM : Inv s.M) (P2 P4 P8 : XIR) :
    rd (semXIR (tp c (toyB 0x4D) L) kindNd4 s).M rF2 = 1 ∧
    rd (semXIR (tp c (toyB 0x4D) L) kindNd4 s).M rF4 = 0 ∧
    rd (semXIR (tp c (toyB 0x4E) L) kindNd4 s).M rF2 = 0 ∧
    rd (semXIR (tp c (toyB 0x4E) L) kindNd4 s).M rF4 = 1 ∧
    pickNd .N8 P2 P4 P8 = P8 := by
  have b2 : byteAt (toyB 0x4D) 0 = 0x4D := rfl
  have b4 : byteAt (toyB 0x4E) 0 = 0x4E := rfl
  obtain ⟨a1, a2, -⟩ := kindNd4_sem c (toyB 0x4D) L (by decide) s hM
  obtain ⟨c1, c2, -⟩ := kindNd4_sem c (toyB 0x4E) L (by decide) s hM
  rw [a1, a2, c1, c2, b2, b4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- (−) **The decode is the kind's**: `N2`'s decode is not `N4`'s (the ladders differ). -/
theorem decF04_ctl : decF04 .N2 ≠ decF04 .N4 := fun h => by
  have e2 := cost_decF04_eq .N2 0
  have e4 := cost_decF04_eq .N4 0
  rw [h] at e2
  rw [e2, (cost_decLevels4 pL4 cw4 cbS4 tw4 0).2.1] at e4
  rw [(cost_decLevels4 pL4 cw4 cbS4 tw4 0).1] at e4
  rw [cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num),
    cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num)] at e4
  revert e4; decide

end FR.X
