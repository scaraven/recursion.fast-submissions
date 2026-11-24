-- New for lvm6 (WP N4-split). V1's transcript values against the stream lanes: the driver's walk (`accOf`)
-- split into per-part segments, and the values of every plain item (`E`, `K`, `G`, `D`, `B`) equal the cells
-- at the circuit's lanes (`layItems`), by a simulation against CA's plan walk.
import Lvm6NodeChildOk

/-!
# V1's values are the stream lanes (WP N4-split, generic part)

* **Segments.** `accOf` is `Prims.walk` of the driver's primitives `PA` (answers read from the trace). Every
  primitive only prepends to the transcript (`AccL`), so the walk of `a ++ b` reads `segV a s` then
  `segV b (nxt a s)` (`segV_append`): `segV its s` are the values the items `its` add from the state `s`.
* **The simulation** (`Inv w s R`): CA's walk state `w` (next entry `w.i`, `w.pend` pending bytes) and V1's
  state `s`: `s` is at entry `w.i`, its cursor is the body of the entries before `w.i` plus the pending bytes,
  the plan from `w.i` on is CA's walk of the rest `R`, and that walk ends well (`ok`, nothing pending). The
  circuit's lane is `laneW w = eLane6 P w.i + 5 + w.pend / 8` (the buffer of entry `w.i`).
* **`simPart`**: for plain items, the values `segV its s` match the slots `layItems its (laneW w)` (`EvMatch`),
  are not openings, the slots' grinds pass (`PowLay`, from `PowLanes6`), and the simulation continues
  after the items with `w.i + queriesOf its` and `pendL its`. `simCap`: a cap moves the cursor only.
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node
open Lvm.QLink (lw laneK slenS)

/-! ## Segments of the driver's transcript -/

section Seg

variable (π : ByteArray) (L : List V.Lev) (tr : Trace)

/-- The state with its transcript cleared. -/
def clr (s : AS) : AS := ({ s.1 with acc := [] }, s.2)

/-- **`f` only prepends to the transcript.** -/
def AccL (f : AS → AS) : Prop :=
  ∀ s : AS, f s = ({ (f (clr s)).1 with acc := (f (clr s)).1.acc ++ s.1.acc }, (f (clr s)).2)

theorem accL_id : AccL (PA π L tr).skip := by
  rintro ⟨⟨⟩, n⟩; rfl

theorem clr_upd (p : AS) (l : List V.NV) : clr ({ p.1 with acc := l }, p.2) = clr p := rfl

theorem accL_seq {f g : AS → AS} (hf : AccL f) (hg : AccL g) : AccL ((PA π L tr).seq f g) := by
  intro s
  show g (f s) = ({ (g (f (clr s))).1 with acc := (g (f (clr s))).1.acc ++ s.1.acc }, (g (f (clr s))).2)
  rw [hf s, hg ({ (f (clr s)).1 with acc := (f (clr s)).1.acc ++ s.1.acc }, (f (clr s)).2), clr_upd,
    hg (f (clr s))]
  simp only [List.append_assoc]

theorem accL_rd (w : ℕ) : AccL ((PA π L tr).rd w) := by
  rintro ⟨⟨⟩, n⟩; rfl

theorem accL_draw (chk : ℕ → Bool) (upd : List ℕ → ℕ → List ℕ) : AccL ((PA π L tr).draw chk upd) := by
  rintro ⟨⟨⟩, n⟩; rfl

theorem accL_cap (ht w : ℕ) : AccL ((PA π L tr).cap ht w) := by
  rintro ⟨⟨⟩, n⟩; rfl

theorem accL_reset : AccL (PA π L tr).reset := by
  rintro ⟨⟨⟩, n⟩; rfl

theorem accL_opn (i : ℕ) : AccL ((PA π L tr).opn i) := by
  rintro ⟨⟨off, buf, st, caps, ps, acc, nr⟩, n⟩
  simp only [PA, clr]
  cases caps[i]? with
  | none => rfl
  | some c => rfl

theorem accL_rep {f : AS → AS} (hf : AccL f) : ∀ m, AccL (V.Prims.rep (PA π L tr) f m)
  | 0 => accL_id π L tr
  | m + 1 => accL_seq π L tr hf (accL_rep hf m)

theorem accL_posRest (ht : ℕ) : ∀ cs, AccL (V.Prims.posRest (PA π L tr) ht cs)
  | [] => accL_id π L tr
  | _ :: cs => accL_seq π L tr (accL_draw π L tr _ _) (accL_posRest ht cs)

theorem accL_item (it : V.Item) : AccL (V.Prims.item (PA π L tr) L it) := by
  cases it with
  | E k => exact accL_rep π L tr (accL_rd π L tr 16) k
  | K k => exact accL_rep π L tr (accL_rd π L tr 8) k
  | cap i => exact accL_cap π L tr _ _
  | G g => exact accL_seq π L tr (accL_rd π L tr 8) (accL_draw π L tr _ _)
  | D k => exact accL_rep π L tr (accL_draw π L tr _ _) k
  | B => exact accL_draw π L tr _ _
  | pos i g =>
    exact accL_seq π L tr (accL_reset π L tr) (accL_seq π L tr (accL_rd π L tr 8)
      (accL_seq π L tr (accL_draw π L tr _ _) (accL_posRest π L tr _ _)))
  | «open» i => exact accL_opn π L tr i

theorem accL_walk : ∀ its : List V.Item, AccL (V.Prims.walk (PA π L tr) L its)
  | [] => accL_id π L tr
  | it :: its => accL_seq π L tr (accL_item π L tr it) (accL_walk its)

/-- The state after the items `its`. -/
def nxt (its : List V.Item) (s : AS) : AS := V.Prims.walk (PA π L tr) L its s

/-- **The values the items `its` add** from the state `s`, oldest first. -/
def segV (its : List V.Item) (s : AS) : List V.Val :=
  ((V.Prims.walk (PA π L tr) L its (clr s)).1.acc.map (V.NV.val π)).reverse

theorem nxt_append : ∀ (a b : List V.Item) (s : AS), nxt π L tr (a ++ b) s = nxt π L tr b (nxt π L tr a s)
  | [], _, _ => rfl
  | it :: a, b, s => nxt_append a b (V.Prims.item (PA π L tr) L it s)

theorem nxt_cons (it : V.Item) (b : List V.Item) (s : AS) : nxt π L tr (it :: b) s = nxt π L tr b (nxt π L tr [it] s) :=
  nxt_append π L tr [it] b s

theorem clr_nxt (its : List V.Item) (s : AS) : clr (nxt π L tr its s) = clr (nxt π L tr its (clr s)) := by
  rw [nxt, accL_walk π L tr its s]; rfl

theorem segV_append (a b : List V.Item) (s : AS) :
    segV π L tr (a ++ b) s = segV π L tr a s ++ segV π L tr b (nxt π L tr a s) := by
  have e := nxt_append π L tr a b (clr s)
  simp only [nxt] at e
  rw [segV, e, accL_walk π L tr b, List.map_append, List.reverse_append]
  rw [segV, segV, clr_nxt]
  rfl

theorem segV_cons (it : V.Item) (b : List V.Item) (s : AS) :
    segV π L tr (it :: b) s = segV π L tr [it] s ++ segV π L tr b (nxt π L tr [it] s) :=
  segV_append π L tr [it] b s

end Seg

/-! ## The values of one item -/

section Items

variable (π : ByteArray) (L : List V.Lev) (tr : Trace)

theorem rep_rd (w : ℕ) : ∀ (m : ℕ) (t : AS),
    (V.Prims.rep (PA π L tr) ((PA π L tr).rd w) m t).1.acc =
      ((List.range m).map fun j ↦ V.NV.rd (t.1.off + w * j) w).reverse ++ t.1.acc ∧
    (V.Prims.rep (PA π L tr) ((PA π L tr).rd w) m t).1.off = t.1.off + w * m ∧
    (V.Prims.rep (PA π L tr) ((PA π L tr).rd w) m t).2 = t.2
  | 0, t => by simp [V.Prims.rep, PA]
  | m + 1, t => by
    obtain ⟨h1, h2, h3⟩ := rep_rd w m (aRd π w t.1, t.2)
    have e : V.Prims.rep (PA π L tr) ((PA π L tr).rd w) (m + 1) t =
      V.Prims.rep (PA π L tr) ((PA π L tr).rd w) m (aRd π w t.1, t.2) := rfl
    rw [e]
    refine ⟨?_, ?_, h3⟩
    · rw [h1]
      have ef : (fun j ↦ V.NV.rd ((aRd π w t.1, t.2).1.off + w * j) w) =
          (fun j ↦ V.NV.rd (t.1.off + w * (j + 1)) w) := by
        funext j; simp only [aRd]; congr 1; ring
      rw [ef, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons, List.append_assoc]
      simp only [aRd, Nat.mul_zero, Nat.add_zero, List.singleton_append]
      rfl
    · rw [h2]; simp only [aRd]; ring

theorem rep_draw (chk : ℕ → Bool) (upd : List ℕ → ℕ → List ℕ) : ∀ (m : ℕ) (t : AS),
    (V.Prims.rep (PA π L tr) ((PA π L tr).draw chk upd) m t).1.acc =
      ((List.range m).map fun j ↦ V.NV.draw (aOf tr (t.2 + j))).reverse ++ t.1.acc ∧
    (V.Prims.rep (PA π L tr) ((PA π L tr).draw chk upd) m t).1.off = t.1.off ∧
    (V.Prims.rep (PA π L tr) ((PA π L tr).draw chk upd) m t).2 = t.2 + m
  | 0, t => by simp [V.Prims.rep, PA]
  | m + 1, t => by
    obtain ⟨h1, h2, h3⟩ := rep_draw chk upd m (aDraw upd (aOf tr t.2) t.1, t.2 + 1)
    have e : V.Prims.rep (PA π L tr) ((PA π L tr).draw chk upd) (m + 1) t =
      V.Prims.rep (PA π L tr) ((PA π L tr).draw chk upd) m (aDraw upd (aOf tr t.2) t.1, t.2 + 1) := rfl
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      have ef : (fun j ↦ V.NV.draw (aOf tr ((aDraw upd (aOf tr t.2) t.1, t.2 + 1).2 + j))) =
          (fun j ↦ V.NV.draw (aOf tr (t.2 + (j + 1)))) := by
        funext j; congr 2; simp only; omega
      rw [ef, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons, List.append_assoc]
      simp only [aDraw, Nat.add_zero, List.singleton_append]
      rfl
    · rw [h2]; rfl
    · rw [h3]; omega

theorem segV_one (it : V.Item) (s : AS) :
    segV π L tr [it] s = ((V.Prims.item (PA π L tr) L it (clr s)).1.acc.map (V.NV.val π)).reverse := rfl

theorem nxt_one (it : V.Item) (s : AS) : nxt π L tr [it] s = V.Prims.item (PA π L tr) L it s := rfl

/-- `E k`: `k` reads of 16 bytes. -/
theorem item_E (k : ℕ) (s : AS) :
    segV π L tr [.E k] s = (List.range k).map (fun j ↦ V.NV.val π (.rd (s.1.off + 16 * j) 16)) ∧
      (nxt π L tr [.E k] s).1.off = s.1.off + 16 * k ∧ (nxt π L tr [.E k] s).2 = s.2 := by
  obtain ⟨a1, -, -⟩ := rep_rd π L tr 16 k (clr s)
  obtain ⟨-, b2, b3⟩ := rep_rd π L tr 16 k s
  refine ⟨?_, b2, b3⟩
  rw [segV_one]
  show ((V.Prims.rep (PA π L tr) ((PA π L tr).rd 16) k (clr s)).1.acc.map (V.NV.val π)).reverse = _
  rw [a1]
  simp [clr, List.map_reverse]

/-- `K k`: `k` reads of 8 bytes. -/
theorem item_K (k : ℕ) (s : AS) :
    segV π L tr [.K k] s = (List.range k).map (fun j ↦ V.NV.val π (.rd (s.1.off + 8 * j) 8)) ∧
      (nxt π L tr [.K k] s).1.off = s.1.off + 8 * k ∧ (nxt π L tr [.K k] s).2 = s.2 := by
  obtain ⟨a1, -, -⟩ := rep_rd π L tr 8 k (clr s)
  obtain ⟨-, b2, b3⟩ := rep_rd π L tr 8 k s
  refine ⟨?_, b2, b3⟩
  rw [segV_one]
  show ((V.Prims.rep (PA π L tr) ((PA π L tr).rd 8) k (clr s)).1.acc.map (V.NV.val π)).reverse = _
  rw [a1]
  simp [clr, List.map_reverse]

/-- `D k`: `k` draws. -/
theorem item_D (k : ℕ) (s : AS) :
    segV π L tr [.D k] s = (List.range k).map (fun j ↦ V.NV.val π (.draw (aOf tr (s.2 + j)))) ∧
      (nxt π L tr [.D k] s).1.off = s.1.off ∧ (nxt π L tr [.D k] s).2 = s.2 + k := by
  obtain ⟨a1, -, -⟩ := rep_draw π L tr V.tt V.keepPs k (clr s)
  obtain ⟨-, b2, b3⟩ := rep_draw π L tr V.tt V.keepPs k s
  refine ⟨?_, b2, b3⟩
  rw [segV_one]
  show ((V.Prims.rep (PA π L tr) ((PA π L tr).draw V.tt V.keepPs) k (clr s)).1.acc.map (V.NV.val π)).reverse = _
  rw [a1]
  simp [clr, List.map_reverse]

/-- `G g`: the nonce, then one draw. -/
theorem item_G (g : ℕ) (s : AS) :
    segV π L tr [.G g] s = [V.NV.val π (.rd s.1.off 8), V.NV.val π (.draw (aOf tr s.2))] ∧
      (nxt π L tr [.G g] s).1.off = s.1.off + 8 ∧ (nxt π L tr [.G g] s).2 = s.2 + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- `B`: one draw. -/
theorem item_B (s : AS) :
    segV π L tr [.B] s = [V.NV.val π (.draw (aOf tr s.2))] ∧
      (nxt π L tr [.B] s).1.off = s.1.off ∧ (nxt π L tr [.B] s).2 = s.2 + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- `cap i`: the cap's shape; the cursor moves past its bytes. -/
theorem item_cap (i : ℕ) (s : AS) :
    segV π L tr [.cap i] s = [.cap (L.getD i default).ht (L.getD i default).wd] ∧
      (nxt π L tr [.cap i] s).1.off =
        s.1.off + 32 * 2 ^ V.capOfL L (L.getD i default).ht (L.getD i default).wd ∧
      (nxt π L tr [.cap i] s).2 = s.2 :=
  ⟨rfl, rfl, rfl⟩

end Items

/-! ## Bytes and lanes -/

section Codec

/-- Byte `i < 8` of lane `j` of the stream. -/
theorem wordsBytes_getD {ws : List Word} {j i : ℕ} (hj : j < ws.length) (hi : i < 8) :
    (wordsBytes ws).getD (8 * j + i) 0 = (wordBytes (ws.getD j 0)).getD i 0 := by
  rw [← Lvm.VEq.getD_drop_bytes, Lvm.QLink.wordsBytes_drop, List.drop_eq_getElem_cons hj,
    Lvm.QLink.wordsBytes_cons, List.getD_append _ _ _ _ (by rw [wordBytes_length]; exact hi),
    List.getD_eq_getElem ws 0 hj]

/-- **A word of the stream read as `K`.** -/
theorem kOf_lane {ws : List Word} {j : ℕ} (hj : j < ws.length) {l : List UInt8}
    (h : ∀ i < 8, l.getD i 0 = (wordsBytes ws).getD (8 * j + i) 0) :
    Lvm.FS.kOfBytes l = FK.toBF64 (laneK ws j) := by
  apply BF64.ext
  apply BitVec.eq_of_toNat_eq
  rw [Lvm.VEq.toNat_kOfBytes]
  have hb : ∀ i : Fin 8, (l.getD i 0).toNat = (ws.getD j 0).toNat / 256 ^ (i : ℕ) % 256 := fun i ↦ by
    rw [h i i.isLt, wordsBytes_getD hj i.isLt, ← ofLE_wordBytes, ofLE_div_mod]
  simp only [hb]
  show _ = (ws.getD j 0).toNat
  have hx := (ws.getD j 0).isLt
  generalize (ws.getD j 0).toNat = x at hx ⊢
  simp only [Fin.sum_univ_eight, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  omega

end Codec

/-! ## The slots' events -/

section Ev

variable {M : Lvm.Loop.Mem} {ws : List Word} (hM : ∀ j < ws.length, M.k j = laneK ws j)
include hM

theorem lk_lane {j : ℕ} (hj : j < ws.length) : lk M j = FK.toBF64 (laneK ws j) := by
  simp only [lk, hM j hj]

theorem kToNat_lk {j : ℕ} (hj : j < ws.length) : LeanVM.Protocol.Verifier.kToNat (lk M j) = lw ws j := by
  rw [lk_lane hM hj]; rfl

/-- Limb `l` of a scalar whose bytes are those of lane `a + l`. -/
theorem limb_lane {B : List UInt8} {a : ℕ} (l : Fin 3) (ha : a + l < ws.length)
    (h : ∀ i < 8, B.getD (8 * l + i) 0 = (wordsBytes ws).getD (8 * (a + l) + i) 0) :
    (Lvm.FS.eOfBytes B).limb l = lk M (a + l) := by
  rw [Lvm6.V.limb_eOfBytes, lk_lane hM ha]
  exact kOf_lane ha fun i hi ↦ by rw [Lvm.VEq.getD_drop_bytes]; exact h i hi

/-- A scalar read: its 16 bytes are lanes `a, a + 1`. -/
theorem evm_e {a : ℕ} (ha : a + 2 ≤ ws.length) {B : List UInt8}
    (h : ∀ i < 16, B.getD i 0 = (wordsBytes ws).getD (8 * a + i) 0) :
    EvM M (.e a) (.read (Lvm.FS.eOfBytes B)) := by
  have h0 := limb_lane hM (B := B) (a := a) 0 (by simp; omega) fun i hi ↦ by
    have := h i (by omega); simpa using this
  have h1 := limb_lane hM (B := B) (a := a) 1 (by simp; omega) fun i hi ↦ by
    have := h (8 + i) (by omega)
    simp only [Fin.val_one]; rw [show 8 * (a + 1) + i = 8 * a + (8 + i) by ring]; simpa using this
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_one] at h0 h1
  show LeanVM.Parameters.e2OfE _ = ev2 M (Lvm.Q2.ld2 a)
  rw [ev2_ld2]
  exact congrArg₂ (fun x y ↦ (⟨x, y⟩ : LeanVM.Parameters.E2)) h0 h1

/-- A word read (a `K` word or a nonce): its 8 bytes are lane `a`. -/
theorem evm_k {a : ℕ} (ha : a < ws.length) {B : List UInt8}
    (h : ∀ i < 8, B.getD i 0 = (wordsBytes ws).getD (8 * a + i) 0) :
    EvM M (.k a) (.read (Lvm.FS.eOfBytes B)) := by
  have h0 := limb_lane hM (B := B) (a := a) 0 (by simpa using ha) fun i hi ↦ by
    have := h i hi; simpa using this
  simp only [Fin.val_zero, Nat.add_zero] at h0
  exact h0

/-- A draw: the answer's bytes are lanes `a, a + 1, a + 2`. -/
theorem evm_d {a g : ℕ} (ha : a + 3 ≤ ws.length) {B : List UInt8}
    (h : ∀ i < 24, B.getD i 0 = (wordsBytes ws).getD (8 * a + i) 0) :
    EvM M (.d a g) (.sample (Lvm.FS.eOfBytes B)) := by
  have hl : ∀ l : Fin 3, (Lvm.FS.eOfBytes B).limb l = lk M (a + l) := fun l ↦
    limb_lane hM l (by have := l.isLt; omega) fun i hi ↦ by
      have := h (8 * l + i) (by have := l.isLt; omega)
      rw [this]; congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · have := hl 0; simpa using this
  · have := hl 1; simpa using this
  · have := hl 2; simpa using this

end Ev

/-! ## Stream bytes: the proof's and the answers' -/

section Stream

variable {P : List PE6} {ws : List Word} (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
include hS hw

/-- **The proof's bytes in a chain entry's buffer are the stream's**: byte `y` of entry `n`'s message
(the query after its 32-byte state) is stream byte `8 · eLane6 n + 40 + y`. -/
theorem pi_getD {n : ℕ} (h1 : 1 ≤ n) (hn : n < P.length) {st g : ℕ} (hk : (P.getD n default).k = .fs st g)
    {y : ℕ} (hy : 32 + y < (P.getD n default).len) :
    (bl (reassemble6 P (decode6 P ws))).getD ((bodyTo (decode6 P ws) P n).length + y) 0 =
      (wordsBytes ws).getD (8 * eLane6 P n + 40 + y) 0 := by
  obtain ⟨R, hR⟩ := body_at (decode6 P ws) P hn
  have hq := bl_qOf6 P ws hn
  have hB := hB6 hw hn
  have hc : contrib6 (decode6 P ws) n (P.getD n default) = (bl (qOf (decode6 P ws) n)).drop 32 := by
    simp only [contrib6, hk]
  have hlen : y < ((bl (qOf (decode6 P ws) n)).drop 32).length := by
    rw [List.length_drop, hq, List.length_take, List.length_drop]; omega
  rw [← Lvm.VEq.getD_drop_bytes, hR, hc, List.getD_append _ _ _ _ hlen, Lvm.VEq.getD_drop_bytes, hq,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, bOff6_eq hS h1 hn.le]
  congr 1; omega

/-- The answer of entry `m` is stream bytes `8 · ansLane6 m …`. -/
theorem ans_getD {m : ℕ} (hm : m < P.length) {x : ℕ} (hx : x < 32) :
    (aOf (decode6 P ws) m).toList.getD x 0 = (wordsBytes ws).getD (8 * ansLane6 P m + x) 0 := by
  rw [aOf_lanes6 hS hw hm, ← Lvm.QLink.wordsBytes_slice, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, ← List.getD_eq_getElem?_getD]

end Stream

/-! ## CA's walk -/

section Walk

variable (lv : ℕ → Lv)

theorem walk_cons (w : WS6) (x : It) (R : List It) :
    walk lv w (x :: R) = ((walkIt lv w x).1 ++ (walk lv (walkIt lv w x).2 R).1, (walk lv (walkIt lv w x).2 R).2) :=
  rfl

/-- **Lookahead**: with bytes pending and a walk that ends well, the next entry is a chain query holding them. -/
theorem first_fs : ∀ (R : List It) (w : WS6), (walk lv w R).2.ok = true → (walk lv w R).2.pend = 0 →
    0 < w.pend → ∃ st g len es, (walk lv w R).1 = ⟨.fs st g, len⟩ :: es ∧ 32 + w.pend ≤ len
  | [], w, _, hp, h0 => by simp only [walk] at hp; omega
  | x :: R, w, hok, hp, h0 => by
    rw [walk_cons] at hok hp ⊢
    cases x with
    | E k =>
      obtain ⟨st, g, len, es, he, hl⟩ := first_fs R _ hok hp (by simp only [walkIt]; omega)
      exact ⟨st, g, len, es, by simpa [walkIt] using he, by simp only [walkIt] at hl; omega⟩
    | K k =>
      obtain ⟨st, g, len, es, he, hl⟩ := first_fs R _ hok hp (by simp only [walkIt]; omega)
      exact ⟨st, g, len, es, by simpa [walkIt] using he, by simp only [walkIt] at hl; omega⟩
    | cap i =>
      obtain ⟨st, g, len, es, he, hl⟩ := first_fs R _ hok hp (by simp only [walkIt]; omega)
      exact ⟨st, g, len, es, by simpa [walkIt] using he, by simp only [walkIt] at hl; omega⟩
    | G g => exact ⟨w.st, g, 40 + w.pend, _, rfl, by omega⟩
    | B => exact ⟨w.st, 0, 32 + w.pend, _, rfl, le_refl _⟩
    | D k =>
      have := walk_ok lv _ R hok
      simp only [walkIt, Bool.and_eq_true, beq_iff_eq] at this
      omega
    | «open» i =>
      have := walk_ok lv _ R hok
      simp only [walkIt] at this
      split at this
      · simp at this
      · simp only [Bool.and_eq_true, beq_iff_eq] at this
        omega

theorem drop_step {P : List PE6} {w : WS6} {x : It} {R : List It} (h : P.drop w.i = (walk lv w (x :: R)).1)
    (hl : w.i + (walkIt lv w x).1.length = (walkIt lv w x).2.i) :
    P.drop (walkIt lv w x).2.i = (walk lv (walkIt lv w x).2 R).1 := by
  rw [← hl, ← List.drop_drop, h, walk_cons, List.drop_left]

theorem getD_of_drop {P : List PE6} {n : ℕ} {e : PE6} {es : List PE6} (h : P.drop n = e :: es) :
    n < P.length ∧ P.getD n default = e := by
  have h0 : (P.drop n)[0]? = some e := by rw [h]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at h0
  refine ⟨(List.getElem?_eq_some_iff.mp h0).1, ?_⟩
  rw [List.getD_eq_getElem?_getD, h0]; rfl

theorem getD_of_drop' {P : List PE6} {n : ℕ} {es rest : List PE6} (h : P.drop n = es ++ rest) {j : ℕ}
    (hj : j < es.length) : n + j < P.length ∧ P.getD (n + j) default = es.getD j default := by
  have h0 : (P.drop n)[j]? = some (es[j]) := by rw [h, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rw [List.getElem?_drop] at h0
  refine ⟨(List.getElem?_eq_some_iff.mp h0).1, ?_⟩
  rw [List.getD_eq_getElem?_getD, h0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

end Walk

/-! ## The simulation -/

theorem getD_take_drop (l : List UInt8) (o n i : ℕ) (hi : i < n) : ((l.drop o).take n).getD i 0 = l.getD (o + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem forall₂_range {α β : Type} {R : α → β → Prop} {f : ℕ → α} {g : ℕ → β} {k : ℕ}
    (h : ∀ j < k, R (f j) (g j)) : List.Forall₂ R ((List.range k).map f) ((List.range k).map g) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact fun j hj ↦ h j (List.mem_range.mp hj)

/-- The items without caps, positions or openings. -/
def plainB : V.Item → Bool
  | .E _ | .K _ | .G _ | .D _ | .B => true
  | _ => false

theorem layItems_cons (it : V.Item) (its : List V.Item) (a : ℕ) :
    layItems (it :: its) a = layItems [it] a ++ layItems its (layEnd [it] a) := by
  cases it <;> simp [layItems, layEnd]

theorem layEnd_cons (it : V.Item) (its : List V.Item) (a : ℕ) :
    layEnd (it :: its) a = layEnd its (layEnd [it] a) := by
  cases it <;> rfl

theorem pendL_cons (L : List V.Lev) (it : V.Item) (its : List V.Item) (n : ℕ) :
    pendL L (it :: its) n = pendL L its (pendL L [it] n) := by
  cases it <;> rfl

theorem queriesOf_cons (L : List V.Lev) (it : V.Item) (its : List V.Item) :
    V.queriesOf L (it :: its) = V.queriesI L it + V.queriesOf L its := by
  simp [V.queriesOf]

section Sim

variable (P : List PE6) (ws : List Word) (lv : ℕ → Lv) (L : List V.Lev) (M : Lvm.Loop.Mem)

local notation "τP" => decode6 P ws
local notation "πP" => reassemble6 P (decode6 P ws)

/-- **The simulation relation** before the items whose CA items are `R`: V1 is at entry `w.i`, its cursor
is the body before `w.i` plus the pending bytes, the plan from `w.i` on is CA's walk of `R`, which ends well. -/
def Inv (w : WS6) (s : AS) (R : List It) : Prop :=
  s.2 = w.i ∧ 2 ≤ w.i ∧ s.1.off = (bodyTo (decode6 P ws) P w.i).length + w.pend ∧ w.pend % 8 = 0 ∧
    P.drop w.i = (walk lv w R).1 ∧ (walk lv w R).2.ok = true ∧ (walk lv w R).2.pend = 0

/-- **The circuit's lane** at `w`: entry `w.i`'s buffer, after the pending bytes. -/
def laneW (w : WS6) : ℕ := eLane6 P w.i + 5 + w.pend / 8

/-- **What the simulation gives** for the items `its` from `(w, s)`, before the CA items `R`. -/
def SimC (its : List V.Item) (w : WS6) (s : AS) (R : List It) : Prop :=
  Inv P ws lv (walk lv w (its.flatMap (itOfs lv))).2 (nxt πP L τP its s) R ∧
    EvMatch M (layItems its (laneW P w)) ((segV πP L τP its s).map toEv) ∧ NoRows (segV πP L τP its s) ∧
    PowLay M (layItems its (laneW P w)) ∧
    layEnd its (laneW P w) = laneW P (walk lv w (its.flatMap (itOfs lv))).2 ∧
    (walk lv w (its.flatMap (itOfs lv))).2.i = w.i + V.queriesOf L its ∧
    (walk lv w (its.flatMap (itOfs lv))).2.pend / 8 = pendL L its (w.pend / 8)

variable {P ws} (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
  {M} (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P ws)

include hS hw hM in
/-- `E k`. -/
theorem sim_E (k : ℕ) {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.E k) ++ R)) :
    SimC P ws lv L M [.E k] w s R := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_E πP L τP k s
  have hW : (walk lv w ([V.Item.E k].flatMap (itOfs lv))).2 = { w with pend := w.pend + 16 * k } := rfl
  change P.drop w.i = (walk lv { w with pend := w.pend + 16 * k } R).1 at hdrop
  change (walk lv { w with pend := w.pend + 16 * k } R).2.ok = true at hok
  change (walk lv { w with pend := w.pend + 16 * k } R).2.pend = 0 at hpe
  unfold SimC
  rw [hW]
  refine ⟨⟨by rw [h2', h2], hi2, by rw [hoff', hoff]; simp only; omega, by simp only; omega, hdrop, hok, hpe⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    simp only [layItems, List.append_nil, List.map_map]
    apply forall₂_range
    intro j hj
    obtain ⟨st, g, len, es, he, hl⟩ := first_fs lv R _ hok hpe (by simp only; omega)
    rw [he] at hdrop
    obtain ⟨hn, hg⟩ := getD_of_drop hdrop
    have hlen := eLane6_bound hS hw (i := w.i) (by omega) hn
    rw [hg] at hlen
    simp only at hl hlen
    simp only [Function.comp, toEv, V.NV.val]
    refine evm_e hM (by simp only [laneW]; omega) fun i hi ↦ ?_
    rw [getD_take_drop _ _ _ _ hi, hoff, show (bodyTo τP P w.i).length + w.pend + 16 * j + i =
      (bodyTo τP P w.i).length + (w.pend + 16 * j + i) by ring,
      pi_getD hS hw (by omega) hn (by rw [hg]) (by rw [hg]; simp only; omega)]
    congr 1; simp only [laneW]; omega
  · rw [hv]
    intro v hv' i ps r
    simp only [List.mem_map, List.mem_range] at hv'
    obtain ⟨j, -, rfl⟩ := hv'
    simp [V.NV.val]
  · intro a g hm
    simp [layItems] at hm
  · simp only [layEnd, laneW]; omega
  · simp [V.queriesOf, V.queriesI]
  · simp only [pendL]; omega

include hS hw hM in
/-- `K k`. -/
theorem sim_K (k : ℕ) {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.K k) ++ R)) :
    SimC P ws lv L M [.K k] w s R := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_K πP L τP k s
  have hW : (walk lv w ([V.Item.K k].flatMap (itOfs lv))).2 = { w with pend := w.pend + 8 * k } := rfl
  change P.drop w.i = (walk lv { w with pend := w.pend + 8 * k } R).1 at hdrop
  change (walk lv { w with pend := w.pend + 8 * k } R).2.ok = true at hok
  change (walk lv { w with pend := w.pend + 8 * k } R).2.pend = 0 at hpe
  unfold SimC
  rw [hW]
  refine ⟨⟨by rw [h2', h2], hi2, by rw [hoff', hoff]; simp only; omega, by simp only; omega, hdrop, hok, hpe⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    simp only [layItems, List.append_nil, List.map_map]
    apply forall₂_range
    intro j hj
    obtain ⟨st, g, len, es, he, hl⟩ := first_fs lv R _ hok hpe (by simp only; omega)
    rw [he] at hdrop
    obtain ⟨hn, hg⟩ := getD_of_drop hdrop
    have hlen := eLane6_bound hS hw (i := w.i) (by omega) hn
    rw [hg] at hlen
    simp only at hl hlen
    simp only [Function.comp, toEv, V.NV.val]
    refine evm_k hM (by simp only [laneW]; omega) fun i hi ↦ ?_
    rw [getD_take_drop _ _ _ _ hi, hoff, show (bodyTo τP P w.i).length + w.pend + 8 * j + i =
      (bodyTo τP P w.i).length + (w.pend + 8 * j + i) by ring,
      pi_getD hS hw (by omega) hn (by rw [hg]) (by rw [hg]; simp only; omega)]
    congr 1; simp only [laneW]; omega
  · rw [hv]
    intro v hv' i ps r
    simp only [List.mem_map, List.mem_range] at hv'
    obtain ⟨j, -, rfl⟩ := hv'
    simp [V.NV.val]
  · intro a g hm
    simp [layItems] at hm
  · simp only [layEnd, laneW]; omega
  · simp [V.queriesOf, V.queriesI]
  · simp only [pendL]; omega

include hw in
/-- A chain entry's contribution is its message. -/
theorem contrib_len {n : ℕ} (hn : n < P.length) {st g len : ℕ} (hg : P.getD n default = ⟨.fs st g, len⟩) :
    (bodyTo τP P (n + 1)).length = (bodyTo τP P n).length + (len - 32) := by
  rw [bodyTo_succ, List.length_append, hg]
  simp only [contrib6]
  have hB := hB6 hw hn
  rw [hg] at hB
  rw [List.length_drop, bl_qOf6 P ws hn, List.length_take, List.length_drop, hg]
  simp only at hB ⊢
  omega

include hS hw hM hpow in
/-- `G g`: the nonce, then the ground draw (its grind from `PowLanes6`). -/
theorem sim_G (g : ℕ) {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.G g) ++ R)) :
    SimC P ws lv L M [.G g] w s R := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_G πP L τP g s
  have hW : (walk lv w ([V.Item.G g].flatMap (itOfs lv))).2 = (walkIt lv w (.G g)).2 := rfl
  have hd' := drop_step lv (P := P) (x := .G g) (R := R) hdrop rfl
  change P.drop w.i = ⟨.fs w.st g, 40 + w.pend⟩ :: (walk lv (walkIt lv w (.G g)).2 R).1 at hdrop
  obtain ⟨hn, hg⟩ := getD_of_drop hdrop
  have hlen := eLane6_bound hS hw (i := w.i) (by omega) hn
  have hsucc := eLane6_succ hS (i := w.i) (by omega) hn
  have hab := ansLane6_bound hS hw hn
  have hans : ansLane6 P w.i = eLane6 P w.i + 1 + (40 + w.pend) / 8 := by
    simp only [ansLane6, hg, (show w.i ≠ 0 by omega), ↓reduceIte]
  have hbody := contrib_len hw hn hg
  rw [hg] at hlen hsucc
  simp only at hlen hsucc
  unfold SimC
  rw [hW]
  refine ⟨⟨by rw [h2']; rw [h2]; rfl, by show 2 ≤ w.i + 1; omega, ?_, by show 0 % 8 = 0; rfl, hd', hok, hpe⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoff', hoff]; show _ = (bodyTo τP P (w.i + 1)).length + 0; rw [hbody]; omega
  · rw [hv]
    simp only [layItems, List.append_nil, List.map_cons, List.map_nil, toEv, V.NV.val]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · refine evm_k hM (by simp only [laneW]; omega) fun i hi ↦ ?_
      rw [getD_take_drop _ _ _ _ hi, hoff, Nat.add_assoc,
        pi_getD hS hw (by omega) hn (by rw [hg]) (by rw [hg]; simp only; omega)]
      congr 1; simp only [laneW]; omega
    · refine evm_d hM (by simp only [laneW]; omega) fun i hi ↦ ?_
      rw [h2, ans_getD hS hw hn (by omega), hans]
      congr 1; simp only [laneW]; omega
  · rw [hv]
    intro v hv' i ps r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl <;> simp [V.NV.val]
  · intro a g' hm
    simp only [layItems, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      false_or, LEv.d.injEq] at hm
    obtain ⟨ha, hgg⟩ := hm
    subst ha
    rw [hgg]
    have hp := hpow w.i hn w.st g (by rw [hg])
    rw [kToNat_lk hM (by simp only [laneW]; omega)]
    rw [hans] at hp
    convert hp using 2
    simp only [laneW]; omega
  · show laneW P w + 10 = eLane6 P (w.i + 1) + 5 + 0 / 8
    rw [hsucc]; simp only [laneW]; omega
  · show w.i + 1 = w.i + V.queriesOf L [.G g]; simp [V.queriesOf, V.queriesI]
  · show 0 / 8 = pendL L [.G g] (w.pend / 8); simp [pendL]

include hS hw hM in
/-- `B`: one draw (no grind). -/
theorem sim_B {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv .B ++ R)) :
    SimC P ws lv L M [.B] w s R := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_B πP L τP s
  have hW : (walk lv w ([V.Item.B].flatMap (itOfs lv))).2 = (walkIt lv w .B).2 := rfl
  have hd' := drop_step lv (P := P) (x := .B) (R := R) hdrop rfl
  change P.drop w.i = ⟨.fs w.st 0, 32 + w.pend⟩ :: (walk lv (walkIt lv w .B).2 R).1 at hdrop
  obtain ⟨hn, hg⟩ := getD_of_drop hdrop
  have hsucc := eLane6_succ hS (i := w.i) (by omega) hn
  have hab := ansLane6_bound hS hw hn
  have hans : ansLane6 P w.i = eLane6 P w.i + 1 + (32 + w.pend) / 8 := by
    simp only [ansLane6, hg, (show w.i ≠ 0 by omega), ↓reduceIte]
  have hbody := contrib_len hw hn hg
  rw [hg] at hsucc
  simp only at hsucc
  unfold SimC
  rw [hW]
  refine ⟨⟨by rw [h2']; rw [h2]; rfl, by show 2 ≤ w.i + 1; omega, ?_, by show 0 % 8 = 0; rfl, hd', hok, hpe⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoff', hoff]; show _ = (bodyTo τP P (w.i + 1)).length + 0; rw [hbody]; omega
  · rw [hv]
    simp only [layItems, List.append_nil, List.map_cons, List.map_nil, toEv, V.NV.val]
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    refine evm_d hM (by simp only [laneW]; omega) fun i hi ↦ ?_
    rw [h2, ans_getD hS hw hn (by omega), hans]
    congr 1; simp only [laneW]; omega
  · rw [hv]
    intro v hv' i ps r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    subst hv'; simp [V.NV.val]
  · intro a g' hm
    simp only [layItems, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, LEv.d.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact (lk M _).toBitVec.isLt
  · show laneW P w + 9 = eLane6 P (w.i + 1) + 5 + 0 / 8
    rw [hsucc]; simp only [laneW]; omega
  · show w.i + 1 = w.i + V.queriesOf L [.B]; simp [V.queriesOf, V.queriesI]
  · show 0 / 8 = pendL L [.B] (w.pend / 8); simp [pendL]

include hS hw hM in
/-- `D k`: `k` further draws (nothing pending, no grind). -/
theorem sim_D (k : ℕ) {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.D k) ++ R)) :
    SimC P ws lv L M [.D k] w s R := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_D πP L τP k s
  have hW : (walk lv w ([V.Item.D k].flatMap (itOfs lv))).2 = (walkIt lv w (.D k)).2 := rfl
  have hd' := drop_step lv (P := P) (x := .D k) (R := R) hdrop (by simp [walkIt])
  change (walk lv (walkIt lv w (.D k)).2 R).2.ok = true at hok
  have hp0 : w.pend = 0 := by
    have := walk_ok lv _ R hok
    simp only [walkIt, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.2
  change P.drop w.i = (List.range k).map (fun m ↦ (⟨.fs (if m = 0 then w.st else w.i + m - 1) 0, 32⟩ : PE6)) ++
    (walk lv (walkIt lv w (.D k)).2 R).1 at hdrop
  have hent : ∀ j < k, w.i + j < P.length ∧ ∃ st, P.getD (w.i + j) default = ⟨.fs st 0, 32⟩ := by
    intro j hj
    obtain ⟨h1, h2⟩ := getD_of_drop' hdrop (j := j) (by simpa using hj)
    refine ⟨h1, if j = 0 then w.st else w.i + j - 1, ?_⟩
    rw [h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have hel : ∀ j ≤ k, eLane6 P (w.i + j) = eLane6 P w.i + 9 * j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      obtain ⟨hn, st, hg⟩ := hent j (by omega)
      have := eLane6_succ hS (i := w.i + j) (by omega) hn
      rw [hg] at this
      rw [← Nat.add_assoc, this, ih (by omega)]
      simp only
      omega
  have hbd : ∀ j ≤ k, (bodyTo τP P (w.i + j)).length = (bodyTo τP P w.i).length := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      obtain ⟨hn, st, hg⟩ := hent j (by omega)
      rw [← Nat.add_assoc, contrib_len hw hn hg, ih (by omega)]
      simp
  unfold SimC
  rw [hW]
  refine ⟨⟨by rw [h2', h2]; rfl, by show 2 ≤ w.i + k; omega, ?_, h8, hd', hok, hpe⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoff', hoff]; show _ = (bodyTo τP P (w.i + k)).length + w.pend; rw [hbd k le_rfl]
  · rw [hv]
    simp only [layItems, List.append_nil, List.map_map]
    apply forall₂_range
    intro j hj
    obtain ⟨hn, st, hg⟩ := hent j hj
    have hab := ansLane6_bound hS hw hn
    have hans : ansLane6 P (w.i + j) = eLane6 P (w.i + j) + 1 + 32 / 8 := by
      simp only [ansLane6, hg, (show w.i + j ≠ 0 by omega), ↓reduceIte]
    rw [hans, hel j hj.le] at hab
    simp only [Function.comp, toEv, V.NV.val]
    refine evm_d hM (by simp only [laneW]; omega) fun i hi ↦ ?_
    rw [h2, ans_getD hS hw hn (by omega), hans, hel j hj.le]
    congr 1; simp only [laneW]; omega
  · rw [hv]
    intro v hv' i ps r
    simp only [List.mem_map, List.mem_range] at hv'
    obtain ⟨j, -, rfl⟩ := hv'
    simp [V.NV.val]
  · intro a g hm
    simp only [layItems, List.append_nil, List.mem_map, List.mem_range, LEv.d.injEq] at hm
    obtain ⟨j, -, -, rfl⟩ := hm
    exact (lk M _).toBitVec.isLt
  · show laneW P w + 9 * k = eLane6 P (w.i + k) + 5 + w.pend / 8
    rw [hel k le_rfl]; simp only [laneW]; omega
  · show w.i + k = w.i + V.queriesOf L [.D k]; simp [V.queriesOf, V.queriesI]
  · show w.pend / 8 = pendL L [.D k] (w.pend / 8); rw [hp0]; rfl

/-- **A cap**: the cursor moves past its bytes, the value is its shape (no slot). -/
theorem sim_cap (i : ℕ) (hcap : V.capOfL L (L.getD i default).ht (L.getD i default).wd = (lv i).lv)
    {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.cap i) ++ R)) :
    Inv P ws lv (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2 (nxt πP L τP [.cap i] s) R ∧
      segV πP L τP [.cap i] s = [.cap (L.getD i default).ht (L.getD i default).wd] ∧
      (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2.i = w.i ∧
      (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2.pend = w.pend + 32 * 2 ^ (lv i).lv := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  obtain ⟨hv, hoff', h2'⟩ := item_cap πP L τP i s
  refine ⟨⟨by rw [h2', h2]; rfl, hi2, ?_, ?_, hdrop, hok, hpe⟩, hv, rfl, rfl⟩
  · rw [hoff', hoff, hcap]
    show (bodyTo τP P w.i).length + w.pend + 32 * 2 ^ (lv i).lv =
      (bodyTo τP P w.i).length + (w.pend + 32 * 2 ^ (lv i).lv)
    ring
  · show (w.pend + 32 * 2 ^ (lv i).lv) % 8 = 0; omega

include hS hw hM hpow in
theorem sim_item (it : V.Item) (hp : plainB it = true) {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s (itOfs lv it ++ R)) : SimC P ws lv L M [it] w s R := by
  cases it with
  | E k => exact sim_E lv L hS hw hM k h
  | K k => exact sim_K lv L hS hw hM k h
  | G g => exact sim_G lv L hS hw hM hpow g h
  | D k => exact sim_D lv L hS hw hM k h
  | B => exact sim_B lv L hS hw hM h
  | _ => simp [plainB] at hp

include hS hw hM hpow in
/-- **The simulation over plain items.** -/
theorem simPart : ∀ (its : List V.Item), (∀ it ∈ its, plainB it = true) → ∀ {w : WS6} {s : AS} {R : List It},
    Inv P ws lv w s (its.flatMap (itOfs lv) ++ R) → SimC P ws lv L M its w s R
  | [], _, w, s, R, h => by
    refine ⟨h, List.Forall₂.nil, ?_, ?_, rfl, ?_, rfl⟩
    · intro v hv
      have e : segV πP L τP [] s = [] := rfl
      rw [e] at hv
      exact absurd hv List.not_mem_nil
    · intro a g hm; simp [layItems] at hm
    · simp [V.queriesOf]; rfl
  | it :: its, hp, w, s, R, h => by
    rw [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨i1, e1, n1, p1, l1, q1, d1⟩ := sim_item lv L hS hw hM hpow it (hp it List.mem_cons_self) h
    rw [List.flatMap_singleton] at i1 l1 q1 d1
    obtain ⟨i2, e2, n2, p2, l2, q2, d2⟩ :=
      simPart its (fun x hx ↦ hp x (List.mem_cons_of_mem _ hx)) i1
    have hW : (walk lv w ((it :: its).flatMap (itOfs lv))).2 =
        (walk lv (walk lv w (itOfs lv it)).2 (its.flatMap (itOfs lv))).2 := by
      rw [List.flatMap_cons, walk_append]
    unfold SimC
    rw [hW, nxt_cons, segV_cons, layItems_cons it its, layEnd_cons it its, pendL_cons L it its,
      queriesOf_cons L it its, l1]
    refine ⟨i2, ?_, ?_, ?_, l2, ?_, d2 ▸ d1 ▸ rfl⟩
    · rw [List.map_append]; exact List.rel_append e1 e2
    · intro v hv; rcases List.mem_append.mp hv with hv | hv
      · exact n1 v hv
      · exact n2 v hv
    · intro a g hm; rcases List.mem_append.mp hm with hm | hm
      · exact p1 a g hm
      · exact p2 a g hm
    · have hq1 : V.queriesOf L [it] = V.queriesI L it := by simp [V.queriesOf]
      rw [q2, q1, hq1]; omega

end Sim

end Lvm6.Node.Split
