-- New for lvm6 (WP C2, CERT-plan link 12): the extractor's witness readers (`Lvm6XExt`: `child6`, `sigLeaf6`, over
-- `leftOf6 lens18 leafLs18 (stW q)` and `sigOf`) are the node theorem's (`Lvm6NodeAsmG`/`Lvm6NodeChild`:
-- `childOf6 trOfS σOfS`, `σlOfS`, over `decode6 P6 (wsS q)` and `sigAt'`), on every stack.
import Lvm6XExt
import Lvm6NodeAsmG
import Lvm6P18Memo

/-!
# The extractor's readers are the node theorem's (WP C2)

Both sides read the stack's `STREAM` slot (33). The words agree (`stW_bridge`: `K.lane` and `FK.ofBF64` are the
same 64 bits). Three facts then close the gap, for **every** stack `q` (no hypothesis):

* **Trace** (`trOfS_eq`): `decode6 P6` reads entries off the stream's bytes at the plan's lengths (`7 :: lens18`)
  from byte 1; `readTrace6 lens18` reads `q₀` from lane 1 and every later entry lane-aligned along `walk 6 lens18`.
  They agree because every later length is `≡ 0 mod 8` and the walk ends inside the `2^19` lanes (`lensOK18`,
  `lanes18`). The bridge is season 1's (`LvmNodeSoundTr`), with `2^19` lanes.
* **Proof** (`reassemble6_eq`): the node theorem's `reassemble6 P6` classifies entry `i` by the plan's kind, the
  extractor's by the query's length (`64`: node, in `leafLs18`: leaf, else a chain query). They agree on a trace
  whose sizes are the plan's when every entry after the seed is `entOk` (`entOk_P18`, one kernel evaluation of the
  plan) and the seed is a chain query (`.fs 0 0`, FORMAT6 v2.5, `drop 32` on both sides).
* **Signatures** (`sigOf_eq_sigAt'`): `sigOf` and `sigAt'` read the same 597 words in the same order.

**`child6_eq`**, **`sigLeaf6_eq`**, and **`extSpec6_eq`** (`ExtSpec6` in the node theorem's readers).
-/

set_option autoImplicit false

namespace Lvm6.Cert

open RecursionFast Lvm Lvm.Replay Lvm.QLink Lvm.QSig Lvm.Wots
open Lvm6.Q (PE6 EK6 planOf contrib6 bodyTo decode6)
open Lvm6.X (lens18 leafLs18 stride6 piece6 pieces6 readTrace6 leftOf6 sigOf child6 sigLeaf6)

/-! ## The stream words -/

/-- The number of lanes of the `STREAM` slot. -/
abbrev nL : ℕ := 2 ^ 19

/-- The stream lanes as the extractor reads them: window word `33 · 2^19 + u`. -/
def Ws (q : Stack) (u : ℕ) : Word := Lvm6.X.stW q (33 * stride6 + u)

/-- **The two stream-word readers agree.** -/
theorem stW_bridge (q : Stack) (j : ℕ) : (Lvm6.Node.Asm.stW q j).val.toBitVec = Ws q j := by
  unfold Lvm6.Node.Asm.stW Ws Lvm6.X.stW
  rw [show QD.streamIdx j = 33 * stride6 + j by simp only [QD.streamIdx, QD.recSlot, stride6]; omega]
  rfl

theorem wsS_eq (q : Stack) : Lvm6.Node.Asm.wsS q = (List.range nL).map (Ws q) :=
  List.map_congr_left fun j _ => stW_bridge q j

/-! ## The trace (season 1's bridge, `2^19` lanes) -/

section Trace

variable (W : ℕ → Word)

theorem ws_slice {a n : ℕ} (h : a + n ≤ nL) : (((List.range nL).map W).drop a).take n = Lvm.X.wsAt W a n := by
  have h' : a + n ≤ 524288 := h
  refine List.ext_getElem (by simp [Lvm.X.wsAt]; omega) fun i h1 h2 => ?_
  simp [Lvm.X.wsAt]

theorem bytes_slice {a n : ℕ} (h : a + n ≤ nL) :
    ((wordsBytes ((List.range nL).map W)).drop (8 * a)).take (8 * n) = wordsBytes (Lvm.X.wsAt W a n) := by
  rw [wordsBytes_slice, ws_slice W h]

theorem getD_bytes {a i : ℕ} (hi : i < 32) (h : a + 4 ≤ nL) :
    (wordsBytes ((List.range nL).map W)).getD (8 * a + i) 0 = (wordsBytes (Lvm.X.wsAt W a 4)).getD i 0 := by
  rw [← bytes_slice W h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    show i < 8 * 4 from by omega, ite_true]

/-- A lane-aligned entry read off the bytes is the lane reader's. -/
theorem entryAt_eq {u len : ℕ} (h8 : len % 8 = 0) (hr : u + 1 + len / 8 + 4 ≤ nL) :
    entryAt (wordsBytes ((List.range nL).map W)) (8 * u) len = Lvm.X.entAt W u len := by
  have hdv : 8 * (len / 8) = len := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h8)
  have hq := bytes_slice W (a := u + 1) (n := len / 8) (by omega)
  rw [hdv, show 8 * (u + 1) = 8 * u + 8 by ring] at hq
  unfold entryAt Lvm.X.entAt
  refine Prod.ext ?_ ?_
  · show (⟨((wordsBytes ((List.range nL).map W)).drop (8 * u + 8)).take len |>.toArray⟩ : ByteArray) =
      Lvm.X.bArr _
    rw [hq]; rfl
  · simp only [Lvm.X.digW]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [show 8 * u + 8 + len + i = 8 * (u + 1 + len / 8) + i by omega]
    exact getD_bytes W hi (by omega)

/-- The entries along a walk. -/
theorem readEntries_walk : ∀ (l : List ℕ) (u : ℕ), (∀ len ∈ l, len % 8 = 0) →
    u + (l.map fun len => 5 + len / 8).sum ≤ nL →
    readEntries (wordsBytes ((List.range nL).map W)) (8 * u) l =
      (Lvm.X.walk u l).map fun x => Lvm.X.entAt W x.1 x.2
  | [], _, _, _ => rfl
  | len :: r, u, h8, hN => by
    have h0 := h8 len (by simp)
    simp only [List.map_cons, List.sum_cons] at hN
    simp only [readEntries, Lvm.X.walk, List.map_cons]
    rw [entryAt_eq W h0 (by omega)]
    congr 1
    rw [show 8 * u + 40 + len = 8 * (u + 5 + len / 8) by omega]
    exact readEntries_walk r _ (fun l hl => h8 l (by simp [hl])) (by omega)

/-- `q₀`'s entry. -/
theorem entryAt_q0 : entryAt (wordsBytes ((List.range nL).map W)) 1 7 = Lvm.X.q0Ent W := by
  unfold entryAt Lvm.X.q0Ent
  refine Prod.ext ?_ ?_
  · have h1 := bytes_slice W (a := 1) (n := 1) (by norm_num)
    have hw : wordsBytes (Lvm.X.wsAt W 1 1) = wordBytes (W 1) := by
      simp [Lvm.X.wsAt, wordsBytes]
    rw [hw] at h1
    show (⟨((wordsBytes ((List.range nL).map W)).drop (1 + 8)).take 7 |>.toArray⟩ : ByteArray) = Lvm.X.bArr _
    rw [← h1, List.drop_take, show 1 + 8 = 8 * 1 + 1 by rfl, List.drop_drop]
    rfl
  · simp only [Lvm.X.digW]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [show 1 + 8 + 7 + i = 8 * 2 + i by omega]
    exact getD_bytes W hi (by norm_num)

end Trace

/-- The plan's lengths: `q₀`'s 7 bytes, then `lens18`. -/
theorem planOf_P18_lens : (planOf P18).map PE6.len = 7 :: lens18 := by
  unfold lens18
  rw [planOf]
  rfl

/-- **The trace readers agree** on every stack. -/
theorem trOfS_eq (q : Stack) : Lvm6.Node.Asm.trOfS q = readTrace6 lens18 (Ws q) := by
  have h8 : ∀ len ∈ lens18, len % 8 = 0 := fun len h => (Lvm6.X.lensOK18 len h).1
  have hN : 6 + (lens18.map fun len => 5 + len / 8).sum ≤ nL := by
    have := Lvm6.X.lanes18
    simp only [Lvm.X.lanesOf] at this
    rw [this]; norm_num
  have hr : ∀ (B : List UInt8) (l : List ℕ), readEntries B 1 (7 :: l) = entryAt B 1 7 :: readEntries B (8 * 6) l :=
    fun _ _ => rfl
  rw [Lvm6.Node.Asm.trOfS, wsS_eq, decode6, planOf_P18_lens, hr, entryAt_q0, readEntries_walk (Ws q) lens18 6 h8 hN]
  rfl

/-! ## The proof bytes -/

/-- An entry after the seed whose kind the extractor's length classifier recovers: a chain query is not 64 bytes
and not a leaf length, a leaf has a leaf length, a node query is 64 bytes; every length is lane-aligned. -/
def entOk (e : PE6) : Bool :=
  e.len % 8 == 0 && match e.k with
  | .fs _ _ => !(e.len == 64) && !(decide (e.len ∈ leafLs18))
  | .leaf => decide (e.len ∈ leafLs18) && !(e.len == 64)
  | .node .. => e.len == 64
  | _ => false

/-- `entOk` with `Nat.beq` (`leafLs18 = [368, 256]`), for the kernel. -/
def entOkF (e : PE6) : Bool :=
  Nat.beq (e.len % 8) 0 && match e.k with
  | .fs _ _ => !(Nat.beq e.len 64) && !(Nat.beq e.len 368 || Nat.beq e.len 256)
  | .leaf => (Nat.beq e.len 368 || Nat.beq e.len 256) && !(Nat.beq e.len 64)
  | .node .. => Nat.beq e.len 64
  | _ => false

theorem entOk_eq_F (e : PE6) : entOk e = entOkF e := by
  have hm : ∀ n : ℕ, decide (n ∈ leafLs18) = (Nat.beq n 368 || Nat.beq n 256) := fun n ↦ by
    rw [Bool.eq_iff_iff]
    simp [leafLs18, Nat.beq_eq]
  rcases e with ⟨k, len⟩
  cases k <;> simp only [entOk, entOkF, hm, Lvm6.Memo.beq_nat]

/-- **Every entry of `P18`'s plan after the seed is `entOk`** (one kernel pass over `planP18`, KDQ). -/
theorem entOk_P18 : ((planOf P18).drop 2).all entOk = true := by
  rw [Lvm6.planOf_P18_eq, show entOk = entOkF from funext entOk_eq_F]
  decide +kernel

theorem planOf_P18_cons : planOf P18 = ⟨.q0, 7⟩ :: ⟨.fs 0 0, Lvm6.seedLen P18⟩ :: (planOf P18).drop 2 := by
  rw [planOf]
  rfl

theorem size_entAt (W : ℕ → Word) (u : ℕ) {len : ℕ} (h8 : len % 8 = 0) :
    (Lvm.X.entAt W u len).1.data.toList.length = len := by
  simp only [Lvm.X.entAt, Lvm.X.bArr_data, wordsBytes_length, Lvm.X.length_wsAt]
  omega

/-- One entry: the plan's contribution is the classifier's piece. -/
theorem contrib6_eq_piece6 {tr : Trace} {i : ℕ} {p : PE6} {e : ByteArray × Digest} (hp : entOk p = true)
    (he : tr.getD i dflt = e) (hs : e.1.data.toList.length = p.len) :
    contrib6 tr i p = piece6 leafLs18 (aOf tr (i - 1)) e := by
  have hq : bl (qOf tr i) = e.1.data.toList := by rw [qOf, he]; rfl
  obtain ⟨k, len⟩ := p
  simp only at hs
  subst hs
  cases k with
  | q0 => simp [entOk] at hp
  | seed => simp [entOk] at hp
  | fs st g =>
    simp [entOk] at hp
    simp [contrib6, piece6, hq, hp]
  | leaf =>
    simp [entOk] at hp
    simp [contrib6, piece6, hq, hp]
  | node pd sh h lvl cap =>
    simp [entOk] at hp
    simp [contrib6, piece6, hq, hp]

/-- The entries along a walk: the plan's contributions are the classifier's pieces. -/
theorem bodyTo_walk (W : ℕ → Word) (tr : Trace) :
    ∀ (Q : List PE6) (u k : ℕ) (prev : Digest), (∀ p ∈ Q, entOk p = true) →
    (∀ j, tr.getD (k + 1 + j) dflt =
      ((Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2).getD j dflt) →
    aOf tr k = prev →
    (List.range Q.length).flatMap (fun j => contrib6 tr (k + 1 + j) (Q.getD j default)) =
      pieces6 leafLs18 prev ((Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2)
  | [], _, _, _, _, _, _ => rfl
  | p :: Q, u, k, prev, hQ, htr, hprev => by
    have hp := hQ p (by simp)
    have h8 : p.len % 8 = 0 := by
      simp only [entOk, Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
    have h0 := htr 0
    simp only [List.map_cons, Lvm.X.walk, List.getD_cons_zero, Nat.add_zero] at h0
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.map_cons, Lvm.X.walk, pieces6]
    congr 1
    · rw [List.getD_cons_zero, Nat.add_zero, contrib6_eq_piece6 hp h0 (size_entAt W u h8),
        show k + 1 - 1 = k by omega, hprev]
    · have ih := bodyTo_walk W tr Q (u + 5 + p.len / 8) (k + 1) (Lvm.X.entAt W u p.len).2
        (fun p' hp' => hQ p' (by simp [hp'])) (fun j => by
          have := htr (j + 1)
          simp only [List.map_cons, Lvm.X.walk, List.getD_cons_succ] at this
          rw [show k + 1 + 1 + j = k + 1 + (j + 1) by omega]
          exact this)
        (by rw [aOf, h0])
      rw [← ih]
      congr 1
      funext j
      simp only [List.getD_cons_succ, Nat.succ_eq_add_one]
      rw [show k + 1 + (j + 1) = k + 1 + 1 + j by omega]

/-- The plan's contributions over `q₀`, the seed and the rest. -/
theorem bodyTo_cons2 (tr : Trace) (p0 p1 : PE6) (Q : List PE6) :
    bodyTo tr (p0 :: p1 :: Q) (p0 :: p1 :: Q).length = contrib6 tr 0 p0 ++ (contrib6 tr 1 p1 ++
      (List.range Q.length).flatMap (fun j => contrib6 tr (1 + 1 + j) (Q.getD j default))) := by
  rw [bodyTo, List.length_cons, List.length_cons, show Q.length + 1 + 1 = 2 + Q.length by omega, List.range_add,
    List.flatMap_append, List.flatMap_map, show List.range 2 = [0, 1] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_cons_zero, List.append_assoc]
  congr 2
  refine congrArg (fun f => List.flatMap f (List.range Q.length)) (funext fun j => ?_)
  rw [show 2 + j = j + 1 + 1 by omega]
  rfl

/-- **The proof readers agree** on a lane-read trace: `q₀`, a chain-query seed, then `entOk` entries. -/
theorem reassemble6_walk (W : ℕ → Word) {p0 p1 : PE6} {Q : List PE6} (h0 : p0.k = .q0) {st g : ℕ}
    (h1 : p1.k = .fs st g) (hQ : ∀ p ∈ Q, entOk p = true) (e0 e1 : ByteArray × Digest) (u : ℕ) :
    Lvm6.Q.reassemble6 (p0 :: p1 :: Q)
        (e0 :: e1 :: (Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2) =
      Lvm6.X.reassemble6 leafLs18
        (e0 :: e1 :: (Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2) := by
  have hb := bodyTo_walk W (e0 :: e1 :: (Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2)
    Q u 1 e1.2 hQ (fun j => by rw [show 1 + 1 + j = j + 1 + 1 by omega]; rfl) rfl
  have c0 : contrib6 (e0 :: e1 :: (Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2) 0 p0 = [] := by
    simp only [contrib6, h0]
  have c1 : contrib6 (e0 :: e1 :: (Lvm.X.walk u (Q.map PE6.len)).map fun x => Lvm.X.entAt W x.1 x.2) 1 p1 =
      e1.1.data.toList.drop 32 := by
    simp only [contrib6, h1]
    rfl
  rw [Lvm6.Q.reassemble6, bodyTo_cons2, c0, c1, hb]
  rfl

/-- **The proof readers agree at `P18`** on any lane-read trace. -/
theorem reassemble6_P18 (W : ℕ → Word) :
    Lvm6.Q.reassemble6 Lvm6.Node.P6 (readTrace6 lens18 W) = Lvm6.X.reassemble6 leafLs18 (readTrace6 lens18 W) := by
  have hL : lens18 = Lvm6.seedLen P18 :: ((planOf P18).drop 2).map PE6.len := by
    have h := planOf_P18_lens
    rw [planOf_P18_cons] at h
    simp only [List.map_cons, List.cons.injEq, true_and] at h
    exact h.symm
  rw [readTrace6, hL, show Lvm6.Node.P6 = _ from planOf_P18_cons]
  exact reassemble6_walk W rfl rfl (List.all_eq_true.mp entOk_P18) (Lvm.X.q0Ent W)
    (Lvm.X.entAt W 6 (Lvm6.seedLen P18)) (6 + 5 + Lvm6.seedLen P18 / 8)

/-! ## The signatures -/

theorem digAt_eq_digW {v : ℕ → FK} {W : ℕ → Word} {a b : ℕ} (h : ∀ l < 4, (v (a + l)).val.toBitVec = W (b + l)) :
    digAt v a = Lvm.X.digW (Lvm.X.wsAt W b 4) := by
  refine Vector.ext fun k hk => ?_
  simp only [digAt, Lvm.X.digW, Vector.getElem_ofFn]
  rw [digOfW_get _ hk, byteW_toNat _ (Nat.mod_lt _ (by norm_num)), ← wordByte_eq_getD, wordByte]
  have hj : k / 8 < 4 := by omega
  simp only [Lvm.X.wsAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, ← h _ hj]
  rfl

/-- **The two signature readers agree** when the cells from `a` hold the words from `b`. -/
theorem sigOf_eq_sigAt' {v : ℕ → FK} {W : ℕ → Word} {a b : ℕ}
    (h : ∀ t < 597, (v (a + t)).val.toBitVec = W (b + t)) : sigOf W b = sigAt' v a := by
  have hd : ∀ o, o + 4 ≤ 597 → digAt v (a + o) = Lvm.X.digW (Lvm.X.wsAt W (b + o) 4) := fun o ho =>
    digAt_eq_digW fun l hl => by simpa only [Nat.add_assoc] using h (o + l) (by omega)
  have e1 : (W b).toNat = (v a).val.toNat := by
    have h0 := h 0 (by norm_num)
    simp only [Nat.add_zero] at h0
    rw [← h0]
    rfl
  have e2 : ((List.range wotsLen).map fun e => Lvm.X.digW (Lvm.X.wsAt W (b + 1 + 4 * e) 4)) =
      (List.range wotsLen).map fun i => digAt v (a + 1 + 4 * i) := by
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    rw [Nat.add_assoc a, Nat.add_assoc b, hd (1 + 4 * i) (by simp only [wotsLen] at this; omega)]
  have e3 : ((List.range sigHeight).map fun e => Lvm.X.digW (Lvm.X.wsAt W (b + 1 + 4 * wotsLen + 4 * e) 4)) =
      (List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t) := by
    refine List.map_congr_left fun t ht => ?_
    have := List.mem_range.mp ht
    rw [show b + 1 + 4 * wotsLen + 4 * t = b + (533 + 4 * t) by simp only [wotsLen]; omega, Nat.add_assoc a,
      hd (533 + 4 * t) (by simp only [sigHeight] at this; omega)]
  rw [sigOf, sigAt', e1, e2, e3]

theorem sigV_bridge (q : Stack) (o t : ℕ) :
    (Lvm6.Node.Asm.sigV q (Lvm6.Node.Dep.sgC + o + t)).val.toBitVec = Ws q (QD.sB + o + t) := by
  rw [Lvm6.Node.Asm.sigV, stW_bridge, show Lvm6.Node.Dep.sgC + o + t - Lvm6.Node.Dep.sgC = o + t by omega,
    Nat.add_assoc]

/-- **`σ'`**: the extractor's reader is the node theorem's. -/
theorem sigOf_child (q : Stack) : sigOf (Lvm6.X.stW q) (33 * stride6 + 2 ^ 18) = Lvm6.Node.Asm.σOfS q := by
  rw [Lvm6.Node.Asm.σOfS]
  refine sigOf_eq_sigAt' fun t _ => ?_
  have := sigV_bridge q 0 t
  rw [Nat.add_zero, Nat.add_zero] at this
  rw [this, Ws, QD.sB, show 33 * stride6 + (2 ^ 18 + t) = 33 * stride6 + 2 ^ 18 + t by ring]

/-! ## The readers -/

/-- **The leaf signature**: the extractor's `sigLeaf6` is the node theorem's `σlOfS`, on every stack. -/
theorem sigLeaf6_eq (q : Stack) : sigLeaf6 q = Lvm6.Node.Asm.σlOfS q := by
  rw [sigLeaf6, Lvm6.Node.Asm.σlOfS]
  refine sigOf_eq_sigAt' fun t _ => ?_
  rw [sigV_bridge q 597 t, Ws, QD.sB, show 33 * stride6 + (2 ^ 18 + 597 + t) = 33 * stride6 + 2 ^ 18 + 597 + t by
    ring]

/-- **The left child**: the extractor's `child6` is the node theorem's `childOf6 trOfS σOfS`, on every stack. -/
theorem child6_eq (q : Stack) : child6 q = Lvm6.Node.childOf6 Lvm6.Node.Asm.trOfS Lvm6.Node.Asm.σOfS q := by
  rw [child6, leftOf6, Lvm6.Node.childOf6, sigOf_child, trOfS_eq q, reassemble6_P18]
  rfl

/-- **`ExtSpec6` in the node theorem's readers** (the form `node6V_final`'s `Stmt.node6V` names). -/
theorem extSpec6_eq (I c x h) : Lvm6.X.ExtSpec6 I c x h = witOf6 (hdrView P18 x) (Lvm6.X.pick6 I h)
    (Lvm6.Node.childOf6 Lvm6.Node.Asm.trOfS Lvm6.Node.Asm.σOfS (Lvm6.X.pick6 I h))
    (Lvm6.Node.Asm.σlOfS (Lvm6.X.pick6 I h)) := by
  rw [Lvm6.X.ExtSpec6, child6_eq, sigLeaf6_eq]

end Lvm6.Cert
