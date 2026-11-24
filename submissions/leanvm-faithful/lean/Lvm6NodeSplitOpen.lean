-- New for lvm6 (WP N4-split, phase 3). The opening's slot facts: V1's opening-phase values (`segO`) match CC's
-- opening slots `layMid₀ ++ … ++ layFin` (`PowLayO`, `OEvMatch`), N4-tail's `htail_of_cc` `hpW heW`.
import Lvm6NodeSplitTail

/-!
# The opening's slots (WP N4-split, phase 3)

* **Generic in the plan** (`P`, `lv`, `L`): `SimO its w s R lay w'` (the simulation `Inv` carried over the items
  `its`, their values matching the opening slots `lay`, grinds passing). `simO_plain` lifts `simPart` to the
  opening slots (`bl`), `simO_cap` a cap (slot `.c ht wd`), `simO_pos` a position group (`G g, D (d−1)`), and
  **`simO_open`** an opening: CA's entries `openPlan6` (leaf, `path` nodes, per opening) put opening `k`'s leaf
  at lane `laneW w − 4 + k · openStride`, so V1's rows (`padRowOf` of the leaf bytes) are `rowsOf M (openRows …)`.
* **Per level** (`LvOk j`, decided once for the five levels of `P18`): `simO_mid` (rounds, high part, cap, bind,
  OOD group, `y`, query group, `λ`, openings) against `layMid j a`, `simO_fin` against `layF a`.
* **`open_slots`**: `PowLayO M layO ∧ OEvMatch M layO ((segO ws).map toEv)`, `layO = layMid 0 a₀ ++ … ++ layF a₄`
  at the lanes `aO j` (`aO 0 = partLane preO`, then each level's end).
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node
open Lvm.QLink (lw laneK slenS)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop LeanVM.Parameters

/-! ## Caps' shapes -/

/-- The shape a cap item records. -/
def capSh (L : List V.Lev) : V.Item → List (ℕ × ℕ)
  | .cap i => [((L.getD i default).ht, (L.getD i default).wd)]
  | _ => []

section CapsSh

variable (π : ByteArray) (L : List V.Lev) (tr : Trace)

theorem item_capsSh (it : V.Item) (s : AS) :
    (nxt π L tr [it] s).1.caps.map (·.2) = s.1.caps.map (·.2) ++ capSh L it := by
  rw [nxt_one]
  cases it with
  | E k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).rd 16) k s).1.caps.map (·.2) = _
    rw [rep_caps π L tr (f := (PA π L tr).rd 16) (fun _ ↦ rfl)]; simp [capSh]
  | K k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).rd 8) k s).1.caps.map (·.2) = _
    rw [rep_caps π L tr (f := (PA π L tr).rd 8) (fun _ ↦ rfl)]; simp [capSh]
  | cap i => simp [V.Prims.item, PA, aCap, capSh]
  | G g => simp [capSh]; rfl
  | D k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).draw V.tt V.keepPs) k s).1.caps.map (·.2) = _
    rw [rep_caps π L tr (f := (PA π L tr).draw V.tt V.keepPs) (fun _ ↦ rfl)]; simp [capSh]
  | B => simp [capSh]; rfl
  | pos i g =>
    show (V.Prims.posRest (PA π L tr) _ _ _).1.caps.map (·.2) = _
    rw [posRest_caps]; simp [capSh]; rfl
  | «open» i =>
    show ((PA π L tr).opn i s).1.caps.map (·.2) = _
    simp only [PA]
    split <;> simp [capSh] <;> rfl

theorem walk_capsSh : ∀ (its : List V.Item) (s : AS),
    (nxt π L tr its s).1.caps.map (·.2) = s.1.caps.map (·.2) ++ its.flatMap (capSh L)
  | [], _ => by simp; rfl
  | it :: its, s => by
    rw [nxt_cons, walk_capsSh its, item_capsSh, List.flatMap_cons, List.append_assoc]

theorem posRest_off (ht : ℕ) : ∀ cs s, (V.Prims.posRest (PA π L tr) ht cs s).1.off = s.1.off
  | [], _ => rfl
  | _ :: cs, s => posRest_off ht cs _

end CapsSh

/-! ## The opening slots along a simulation -/

section SimO

variable (P : List PE6) (ws : List Word) (lv : ℕ → Lv) (L : List V.Lev) (M : Mem)

set_option hygiene false in
local notation "τP" => decode6 P ws
set_option hygiene false in
local notation "πP" => reassemble6 P (decode6 P ws)

/-- **The simulation over `its`, against opening slots `lay`**, from `(w, s)` to `w'`. -/
def SimO (its : List V.Item) (w : WS6) (s : AS) (R : List It) (lay : List QC.OEv) (w' : WS6) : Prop :=
  Inv P ws lv w' (nxt πP L τP its s) R ∧ QC.OEvMatch M lay ((segV πP L τP its s).map toEv) ∧ QC.PowLayO M lay

variable {P ws lv L M}

theorem simO_append {a b : List V.Item} {w w1 w2 : WS6} {s : AS} {R : List It} {la lb : List QC.OEv}
    (ha : SimO P ws lv L M a w s (b.flatMap (itOfs lv) ++ R) la w1)
    (hb : SimO P ws lv L M b w1 (nxt πP L τP a s) R lb w2) :
    SimO P ws lv L M (a ++ b) w s R (la ++ lb) w2 := by
  obtain ⟨-, e1, p1⟩ := ha
  obtain ⟨i2, e2, p2⟩ := hb
  refine ⟨by rw [nxt_append]; exact i2, by rw [segV_append, List.map_append]; exact List.rel_append e1 e2, ?_⟩
  intro x g hm
  rcases List.mem_append.mp hm with hm | hm
  · exact p1 x g hm
  · exact p2 x g hm

theorem simO_eq {its : List V.Item} {w w' : WS6} {s : AS} {R : List It} {l l' : List QC.OEv} (h : l = l')
    (hs : SimO P ws lv L M its w s R l w') : SimO P ws lv L M its w s R l' w' := h ▸ hs

variable (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P ws)

include hS hw hM hpow in
/-- **Plain items** on the opening slots (`bl` of their `layItems`). -/
theorem simO_plain (its : List V.Item) (hp : ∀ it ∈ its, plainB it = true) {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s (its.flatMap (itOfs lv) ++ R)) :
    SimO P ws lv L M its w s R (QC.bl (layItems its (laneW P w))) (walk lv w (its.flatMap (itOfs lv))).2 ∧
      layEnd its (laneW P w) = laneW P (walk lv w (its.flatMap (itOfs lv))).2 := by
  obtain ⟨i1, e1, -, p1, l1, -, -⟩ := simPart lv L hS hw hM hpow its hp h
  exact ⟨⟨i1, oevMatch_bl e1, powLayO_bl p1⟩, l1⟩

/-- **A cap**: the value `.cap ht wd`, the slot `.c ht wd`. -/
theorem simO_cap (i : ℕ) (hcap : V.capOfL L (L.getD i default).ht (L.getD i default).wd = (lv i).lv)
    {w : WS6} {s : AS} {R : List It} (h : Inv P ws lv w s (itOfs lv (.cap i) ++ R)) :
    SimO P ws lv L M [.cap i] w s R [.c (L.getD i default).ht (L.getD i default).wd]
      (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2 ∧
      (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2.i = w.i ∧
      (walk lv w ([V.Item.cap i].flatMap (itOfs lv))).2.pend = w.pend + 32 * 2 ^ (lv i).lv := by
  obtain ⟨i1, hv, q1, d1⟩ := sim_cap lv L i hcap h
  refine ⟨⟨i1, ?_, ?_⟩, q1, d1⟩
  · rw [hv]
    exact List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil
  · intro a g hm; simp at hm

end SimO

/-! ## The entries of an opening -/

theorem len_flatMap_range {α : Type} (g : ℕ → List α) (c : ℕ) (hg : ∀ k, (g k).length = c) :
    ∀ t, ((List.range t).flatMap g).length = t * c
  | 0 => by simp
  | t + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      len_flatMap_range g c hg t, hg, Nat.succ_mul]

theorem getD_flatMap_range {α : Type} [Inhabited α] (g : ℕ → List α) (c : ℕ) (hg : ∀ k, (g k).length = c) :
    ∀ (t k m : ℕ), k < t → m < c → ((List.range t).flatMap g).getD (k * c + m) default = (g k).getD m default
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | t + 1, k, m, hk, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen := len_flatMap_range g c hg t
    by_cases hkt : k < t
    · have : (k + 1) * c ≤ t * c := Nat.mul_le_mul_right _ hkt
      rw [List.getD_append _ _ _ _ (by rw [hlen]; rw [Nat.succ_mul] at this; omega)]
      exact getD_flatMap_range g c hg t k m hkt hm
    · have hk' : k = t := by omega
      subst hk'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

section Open

variable {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem}

set_option hygiene false in
local notation "τP" => decode6 P ws
set_option hygiene false in
local notation "πP" => reassemble6 P (decode6 P ws)

variable (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
  (hM : ∀ j < ws.length, M.k j = laneK ws j)

include hw in
theorem contrib_leaf {n : ℕ} (hn : n < P.length) {len : ℕ} (hg : P.getD n default = ⟨.leaf, len⟩) :
    (bodyTo τP P (n + 1)).length = (bodyTo τP P n).length + len := by
  rw [bodyTo_succ, List.length_append, hg]
  simp only [contrib6]
  have hB := hB6 hw hn
  rw [hg] at hB
  rw [bl_qOf6 P ws hn, List.length_take, List.length_drop, hg]
  simp only at hB ⊢
  omega

include hw in
theorem contrib_node {n : ℕ} (hn : n < P.length) {pd sh h lvl : ℕ} {cap : Option (ℕ × ℕ × ℕ)}
    (hg : P.getD n default = ⟨.node pd sh h lvl cap, 64⟩) :
    (bodyTo τP P (n + 1)).length = (bodyTo τP P n).length + 32 := by
  rw [bodyTo_succ, List.length_append, hg]
  have hB := hB6 hw hn
  rw [hg] at hB
  have hq : (bl (qOf τP n)).length = 64 := by
    rw [bl_qOf6 P ws hn, List.length_take, List.length_drop, hg]; simp only at hB ⊢; omega
  simp only [contrib6]
  split <;> simp [hq]

include hS hw in
/-- A leaf entry's contribution is its query: byte `y` is stream byte `8 · eLane6 n + 8 + y`. -/
theorem pi_leaf {n : ℕ} (h1 : 1 ≤ n) (hn : n < P.length) {len : ℕ} (hg : P.getD n default = ⟨.leaf, len⟩)
    {y : ℕ} (hy : y < len) :
    (bl πP).getD ((bodyTo τP P n).length + y) 0 = (wordsBytes ws).getD (8 * eLane6 P n + 8 + y) 0 := by
  obtain ⟨R, hR⟩ := body_at τP P hn
  have hq := bl_qOf6 P ws hn
  have hB := hB6 hw hn
  rw [hg] at hB hq
  have hc : contrib6 τP n (P.getD n default) = bl (qOf τP n) := by rw [hg]; rfl
  have hlen : y < (bl (qOf τP n)).length := by
    rw [hq, List.length_take, List.length_drop]; simp only at hB ⊢; omega
  rw [← Lvm.VEq.getD_drop_bytes, hR, hc, List.getD_append _ _ _ _ hlen, hq,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hy, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, bOff6_eq hS h1 hn.le]

include hS hw in
/-- The lanes and body bytes of `k` openings (a leaf of `lf` bytes, `p` nodes each). -/
theorem open_geo {n0 : ℕ} (h1 : 1 ≤ n0) {es rest : List PE6} {lf p t : ℕ} (hd : P.drop n0 = es ++ rest)
    (hlen : es.length = t * (1 + p))
    (hes : ∀ k < t, ∀ m < 1 + p, ∃ e, es.getD (k * (1 + p) + m) default = e ∧
      (m = 0 → e = ⟨.leaf, lf⟩) ∧ (0 < m → ∃ pd sh h lvl cap, e = ⟨.node pd sh h lvl cap, 64⟩)) :
    ∀ k ≤ t, eLane6 P (n0 + k * (1 + p)) = eLane6 P n0 + k * (5 + lf / 8 + 13 * p) ∧
      (bodyTo τP P (n0 + k * (1 + p))).length = (bodyTo τP P n0).length + k * (lf + 32 * p) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hb : ∀ m ≤ p, k * (1 + p) + m < es.length := by
      intro m hm
      rw [hlen]
      have : (k + 1) * (1 + p) ≤ t * (1 + p) := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this
      omega
    have inner : ∀ m ≤ p, eLane6 P (n0 + k * (1 + p) + 1 + m) = eLane6 P (n0 + k * (1 + p)) + 5 + lf / 8 + 13 * m ∧
        (bodyTo τP P (n0 + k * (1 + p) + 1 + m)).length = (bodyTo τP P (n0 + k * (1 + p))).length + lf + 32 * m := by
      intro m hm
      induction m with
      | zero =>
        obtain ⟨e, he, hl, -⟩ := hes k (by omega) 0 (by omega)
        have hl' := hl rfl
        subst hl'
        obtain ⟨hn, hg⟩ := getD_of_drop' hd (j := k * (1 + p) + 0) (hb 0 (by omega))
        rw [he] at hg
        rw [Nat.add_zero] at hn hg
        have := eLane6_succ hS (i := n0 + k * (1 + p)) (by omega) hn
        rw [hg] at this
        simp only at this
        show eLane6 P (n0 + k * (1 + p) + 1) = _ ∧ (bodyTo τP P (n0 + k * (1 + p) + 1)).length = _
        constructor
        · rw [this]; omega
        · rw [contrib_leaf hw hn hg]; omega
      | succ m ihm =>
        obtain ⟨a1, a2⟩ := ihm (by omega)
        obtain ⟨e, he, -, hn2⟩ := hes k (by omega) (m + 1) (by omega)
        obtain ⟨pd, sh, h, lvl, cap, rfl⟩ := hn2 (by omega)
        obtain ⟨hn, hg⟩ := getD_of_drop' hd (j := k * (1 + p) + (m + 1)) (hb (m + 1) hm)
        rw [he] at hg
        have e : n0 + (k * (1 + p) + (m + 1)) = n0 + k * (1 + p) + 1 + m := by omega
        rw [e] at hn hg
        have := eLane6_succ hS (i := n0 + k * (1 + p) + 1 + m) (by omega) hn
        rw [hg] at this
        simp only at this
        have e2 : n0 + k * (1 + p) + 1 + (m + 1) = n0 + k * (1 + p) + 1 + m + 1 := by omega
        rw [e2]
        constructor
        · rw [this, a1]; omega
        · rw [contrib_node hw hn hg, a2]; omega
    obtain ⟨b1, b2⟩ := inner p le_rfl
    have e3 : n0 + (k + 1) * (1 + p) = n0 + k * (1 + p) + 1 + p := by rw [Nat.succ_mul]; omega
    have m1 : (k + 1) * (5 + lf / 8 + 13 * p) = k * (5 + lf / 8 + 13 * p) + (5 + lf / 8 + 13 * p) :=
      Nat.succ_mul _ _
    have m2 : (k + 1) * (lf + 32 * p) = k * (lf + 32 * p) + (lf + 32 * p) := Nat.succ_mul _ _
    rw [e3, b1, b2, ih1, ih2, m1, m2]
    constructor <;> omega

end Open

/-! ## An opening -/

section OpenStep

variable {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem}

set_option hygiene false in
local notation "τP" => decode6 P ws
set_option hygiene false in
local notation "πP" => reassemble6 P (decode6 P ws)

theorem inv_congr {w : WS6} {s s' : AS} {R : List It} (h2 : s'.2 = s.2) (ho : s'.1.off = s.1.off)
    (h : Inv P ws lv w s R) : Inv P ws lv w s' R := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨h2.trans a, b, ho.trans c, d, e, f, g⟩

/-- The entries of `openPlan6`: a leaf, then `path` nodes, per opening. -/
theorem openPlan6_entries (Lv0 : Lv) (pd0 ce co : ℕ) :
    (openPlan6 Lv0 pd0 ce co).length = Lv0.t * (1 + Lv0.path) ∧
    ∀ k < Lv0.t, ∀ m < 1 + Lv0.path, ∃ e, (openPlan6 Lv0 pd0 ce co).getD (k * (1 + Lv0.path) + m) default = e ∧
      (m = 0 → e = ⟨.leaf, Lv0.leaf⟩) ∧ (0 < m → ∃ pd sh h lvl cap, e = ⟨.node pd sh h lvl cap, 64⟩) := by
  have hg : ∀ j, ((fun j ↦ (⟨.leaf, Lv0.leaf⟩ : PE6) :: (List.range Lv0.path).map fun lvl ↦
      (⟨.node (pd0 + j / ppa Lv0.ht) (j % ppa Lv0.ht * Lv0.ht) Lv0.ht lvl
        (if lvl + 1 = Lv0.path then some (ce, co, Lv0.path) else none), 64⟩ : PE6)) j).length = 1 + Lv0.path := by
    intro j; simp [Nat.add_comm]
  refine ⟨len_flatMap_range _ _ hg _, fun k hk m hm ↦ ⟨_, getD_flatMap_range _ _ hg _ k m hk hm, ?_, ?_⟩⟩
  · rintro rfl; rfl
  · intro hm0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_range (show m' < Lv0.path by omega), Option.map_some, Option.getD_some]
    exact ⟨_, _, _, _, _, rfl⟩

variable (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
  (hM : ∀ j < ws.length, M.k j = laneK ws j)

include hS hw hM in
/-- **An opening** of commitment `i` (its cap of shape `(ht, wd)` read, `t` positions): the value
`.rows i ps r` with `r` the rows the opening slot reads at lane `laneW w − 4` (`openRows lev wd`). -/
theorem simO_open (i : ℕ) {lev : Level} {wd o : ℕ} {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s (itOfs lv (.open i) ++ R)) (hps : s.1.ps.length = (lv i).t)
    (hcap : s.1.caps[i]? = some (o, (L.getD i default).ht, wd))
    (hht : (L.getD i default).ht = (lv i).ht) (hcl : V.capOfL L (L.getD i default).ht wd = (lv i).lv)
    (hlf : 8 * min (V.occL L (L.getD i default).ht wd) wd = (lv i).leaf)
    (hlev : lev.leafB = (lv i).leaf ∧ lev.ht = (lv i).ht ∧ lev.lv = (lv i).lv) :
    ∃ w', SimO P ws lv L M [.open i] w s R [.o (QC.openRows lev wd (laneW P w - 4) (lv i).t)] w' ∧
      laneW P w' = laneW P w + (lv i).t * QC.openStride lev := by
  obtain ⟨h2, hi2, hoff, h8, hdrop, hok, hpe⟩ := h
  have hok' := walk_ok lv _ R hok
  cases hf : w.caps.find? (·.1 == i) with
  | none =>
    exfalso
    simp [walkIt, hf] at hok'
  | some x =>
    obtain ⟨l, ce, co, nb⟩ := x
    have hwi : walkIt lv w (.open i) = (openPlan6 (lv i) (w.i - 1 - (lv i).gap - ((lv i).d - 1)) ce co,
        { w with i := w.i + (lv i).t * (1 + (lv i).path), run := 0,
                 ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && decide (1 ≤ (lv i).d) &&
                   decide ((lv i).d + (lv i).gap = w.run) && decide (1 ≤ (lv i).path) &&
                   decide ((lv i).lv ≤ (lv i).ht) && decide (1 ≤ (lv i).ht) && decide ((lv i).ht ≤ 128) &&
                   decide (nb = 32 * 2 ^ (lv i).lv) }) := by
      simp only [walkIt, hf]
    rw [hwi] at hok'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
    have hp0 : w.pend = 0 := hok'.1.1.1.1.1.1.1.1.2
    have hpath : 1 ≤ (lv i).path := hok'.1.1.1.1.2
    set Lv0 := lv i with hLv0
    obtain ⟨hlenE, hes⟩ := openPlan6_entries Lv0 (w.i - 1 - Lv0.gap - (Lv0.d - 1)) ce co
    have hdrop' : P.drop w.i = openPlan6 Lv0 (w.i - 1 - Lv0.gap - (Lv0.d - 1)) ce co ++
        (walk lv (walkIt lv w (.open i)).2 R).1 := by
      rw [hdrop, show itOfs lv (.open i) ++ R = It.open i :: R from rfl, walk_cons, hwi]
    have geo := open_geo hS hw (n0 := w.i) (by omega) hdrop' hlenE hes
    obtain ⟨gE, gB⟩ := geo Lv0.t le_rfl
    -- V1's side
    have hpe' : Lv0.path = (L.getD i default).ht - V.capOfL L (L.getD i default).ht wd := by
      rw [hcl, hht]; rfl
    have hopn : opnB L (L.getD i default).ht wd = Lv0.leaf + 32 * Lv0.path := by
      rw [opnB, hlf, hpe']
    have hv : segV πP L τP [.open i] s = [V.NV.val πP (.rows i s.1.ps wd (V.occL L (L.getD i default).ht wd)
        (8 * min (V.occL L (L.getD i default).ht wd) wd)
        ((List.range s.1.ps.length).map fun j ↦ s.1.off + j * opnB L (L.getD i default).ht wd))] := by
      rw [segV_one]
      show ((((PA πP L τP).opn i (clr s)).1.acc.map (V.NV.val πP)).reverse = _)
      simp only [PA, clr, hcap]
      rfl
    have hn : nxt πP L τP [.open i] s = (aOpn L i (L.getD i default).ht wd s.1,
        s.2 + s.1.ps.length * (1 + ((L.getD i default).ht - V.capOfL L (L.getD i default).ht wd))) := by
      rw [nxt_one]
      show (PA πP L τP).opn i s = _
      simp only [PA, hcap]
    rw [hopn] at hv
    refine ⟨(walkIt lv w (.open i)).2, ⟨⟨?_, ?_, ?_, ?_, ?_, hok, hpe⟩, ?_, ?_⟩, ?_⟩
    · rw [hn, hwi]; show s.2 + _ = w.i + _; rw [h2, hps, ← hpe']
      all_goals first | rfl | exact Or.inl rfl | simp [hp]
    · rw [hwi]; show 2 ≤ w.i + _; omega
    · rw [hn, hwi]
      show s.1.off + s.1.ps.length * opnB L _ wd = (bodyTo τP P (w.i + Lv0.t * (1 + Lv0.path))).length + w.pend
      rw [hps, hopn, hoff, gB, hp0]; ring
    · rw [hwi]; show w.pend % 8 = 0; exact h8
    · have hds := drop_step lv (P := P) (x := .open i) (R := R) hdrop (by
        rw [hwi]; show w.i + (openPlan6 _ _ _ _).length = w.i + Lv0.t * (1 + Lv0.path); rw [hlenE])
      exact hds
    · rw [hv]
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      show _ = QC.rowsOf M _
      simp only [QC.rowsOf, QC.openRows, List.map_map]
      apply List.ext_getElem (by simp [hps])
      intro k hk1 hk2
      simp only [List.length_map, List.length_range] at hk1
      rw [hps] at hk1
      simp only [List.getElem_map, List.getElem_range, Function.comp]
      -- one row
      have hm8 : min (V.occL L (L.getD i default).ht wd) wd = lev.leafB / 8 := by
        rw [hlev.1, ← hlf]; omega
      simp only [Lvm.FS.padRowOf, hm8, QC.openRow, List.map_append, List.map_replicate, List.map_map]
      congr 1
      simp only [Lvm.FS.rowOf]
      · apply List.map_congr_left
        intro jj hjj
        simp only [List.mem_range] at hjj
        simp only [Function.comp, QC.lw]
        -- the entry `w.i + k (1 + Lv0.path)` is the `k`-th leaf
        obtain ⟨gEk, gBk⟩ := geo k hk1.le
        obtain ⟨e, he, hl, -⟩ := hes k hk1 0 (by omega)
        have hl' := hl rfl; subst hl'
        obtain ⟨hnk, hgk⟩ := getD_of_drop' hdrop' (j := k * (1 + Lv0.path) + 0) (by
          rw [hlenE]; have : (k + 1) * (1 + Lv0.path) ≤ Lv0.t * (1 + Lv0.path) := Nat.mul_le_mul_right _ hk1
          rw [Nat.succ_mul] at this; omega)
        rw [he, Nat.add_zero] at hgk
        rw [Nat.add_zero] at hnk
        have hlen := eLane6_bound hS hw (i := w.i + k * (1 + Lv0.path)) (by omega) hnk
        rw [hgk] at hlen
        simp only at hlen
        have hjl : 8 * jj + 8 ≤ Lv0.leaf := by rw [← hlev.1]; omega
        have hstr : QC.openStride lev = 5 + Lv0.leaf / 8 + 13 * Lv0.path := by
          simp only [QC.openStride, hlev.1, hlev.2.1, hlev.2.2, Lv.path]; omega
        have hlw : laneW P w = eLane6 P w.i + 5 := by simp only [laneW, hp0]
        rw [lk_lane hM (by rw [hlw, hstr]; omega)]
        refine (kOf_lane (by rw [hlw, hstr]; omega) fun x hx ↦ ?_)
        rw [getD_take_drop _ _ _ _ hx, getD_take_drop _ _ _ _ (by omega), hoff, hp0,
          show (bodyTo τP P w.i).length + 0 + k * (Lv0.leaf + 32 * Lv0.path) + (8 * jj + x) =
            (bodyTo τP P (w.i + k * (1 + Lv0.path))).length + (8 * jj + x) by rw [gBk]; ring,
          pi_leaf hS hw (by omega) hnk hgk (by omega), gEk]
        congr 1
        rw [hlw, hstr]
        omega
    · intro a g hm; simp at hm
    · simp only [laneW, hwi, hp0]
      show eLane6 P (w.i + Lv0.t * (1 + Lv0.path)) + 5 + 0 / 8 = _
      rw [gE]
      simp only [QC.openStride, hlev.1, hlev.2.1, hlev.2.2, Lv.path]
      ring_nf

include hS hw hM in
/-- **A position group** `pos i g` as `G g, D (d − 1)` (values, cursor and entry). -/
theorem simO_pos (hpow : PowLanes6 P ws) (i g : ℕ) {w : WS6} {s : AS} {R : List It}
    (hd : V.Lev.draws (L.getD i default) = (lv i).d) (hp1 : 1 ≤ V.Lev.per (L.getD i default))
    (ht1 : 1 ≤ (L.getD i default).t) (h : Inv P ws lv w s (itOfs lv (.pos i g) ++ R)) :
    SimO P ws lv L M [.pos i g] w s R (QC.bl (layItems [.G g, .D ((lv i).d - 1)] (laneW P w)))
        (walk lv w ([V.Item.G g, .D ((lv i).d - 1)].flatMap (itOfs lv))).2 ∧
      layEnd [.G g, .D ((lv i).d - 1)] (laneW P w) =
        laneW P (walk lv w ([V.Item.G g, .D ((lv i).d - 1)].flatMap (itOfs lv))).2 := by
  have hd1 : 1 ≤ (lv i).d := by rw [← hd]; exact le_max_left _ _
  obtain ⟨⟨i1, e1, p1⟩, l1⟩ := simO_plain hS hw hM hpow (L := L) [.G g, .D ((lv i).d - 1)]
    (by intro it hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl <;> rfl) (R := R) h
  obtain ⟨v1, n1, -, -⟩ := item_pos πP L τP (i := i) (g := g) hp1 ht1 s
  have hseg : segV πP L τP [.pos i g] s = segV πP L τP [.G g, .D ((lv i).d - 1)] s := by
    rw [v1, segV_cons, (item_G πP L τP g s).1, (item_D πP L τP _ _).1, (item_G πP L τP g s).2.2, hd]
    rw [show (lv i).d = ((lv i).d - 1) + 1 by omega, List.range_succ_eq_map]
    simp only [Nat.add_sub_cancel, List.map_cons, List.map_map, Nat.add_zero, List.cons_append]
    congr 2
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    congr 3
    omega
  have hoff : (nxt πP L τP [.pos i g] s).1.off = (nxt πP L τP [.G g, .D ((lv i).d - 1)] s).1.off := by
    rw [nxt_cons πP L τP (.G g) [.D ((lv i).d - 1)] s, (item_D πP L τP _ _).2.1, (item_G πP L τP g s).2.1, nxt_one]
    show (V.Prims.posRest (PA πP L τP) _ _ _).1.off = _
    rw [posRest_off]; rfl
  have h2 : (nxt πP L τP [.pos i g] s).2 = (nxt πP L τP [.G g, .D ((lv i).d - 1)] s).2 := by
    rw [n1, nxt_cons πP L τP (.G g) [.D ((lv i).d - 1)] s, (item_D πP L τP _ _).2.2, (item_G πP L τP g s).2.2, hd]
    omega
  exact ⟨⟨inv_congr h2 hoff i1, by rw [hseg]; exact e1, p1⟩, l1⟩

end OpenStep

/-! ## One level, generic in its parameters -/

/-- **A mid level's parameters** (FORMAT6 §6.6 `levelPart j`; CC's `layRounds`, `layTail`). -/
structure MidP where
  /-- The level's index. -/
  j : ℕ
  /-- The fold rounds' grind and their number (`= nh`, the high part's scalars). -/
  g : ℕ
  ℓ : ℕ
  /-- The OOD group's further draws, the query group's further draws, the openings. -/
  ko : ℕ
  kq : ℕ
  t : ℕ
  /-- The OOD and query grinds. -/
  gO : ℕ
  gQ : ℕ
  /-- The next commitment's height, width and cap level. -/
  ht : ℕ
  wd : ℕ
  lvN : ℕ
  /-- This commitment's width and level. -/
  wdI : ℕ
  lev : Level

/-- The rounds and the high part (plain). -/
def MidP.pre (q : MidP) : List V.Item := rep q.ℓ [.E 4, .G q.g, .D 1] ++ [.E q.ℓ]

/-- The bind, the OOD group and `y` (plain). -/
def MidP.ood (q : MidP) : List V.Item := [.B, .G q.gO, .D q.ko, .E 1]

/-- **The level's items** (V1's schedule). -/
def MidP.items (q : MidP) : List V.Item :=
  q.pre ++ ([.cap (q.j + 1)] ++ (q.ood ++ ([.pos q.j q.gQ] ++ ([.D 1] ++ [.open q.j]))))

/-- **The level's opening slots** from lane `a` (CC's `layRounds`, `layTail`). -/
def MidP.lay (q : MidP) (a : ℕ) : List QC.OEv :=
  QC.layRounds q.g q.ℓ a ++ QC.layTail q.ℓ q.ko q.kq q.t q.lev q.wdI q.ht q.wd q.lvN q.gO q.gQ (a + 27 * q.ℓ)

/-- The lane after the level (after its openings). -/
def MidP.aEnd (q : MidP) (a : ℕ) : ℕ :=
  QC.tailOpenAt q.ℓ q.ko q.kq q.lvN (a + 27 * q.ℓ) + q.t * QC.openStride q.lev

/-- **What a mid level's parameters must meet** against V1's levels `L` and CA's `lv`. -/
structure MidOk (L : List V.Lev) (lv : ℕ → Lv) (q : MidP) : Prop where
  draws : V.Lev.draws (L.getD q.j default) = (lv q.j).d
  kq : q.kq + 1 = (lv q.j).d
  per : 1 ≤ V.Lev.per (L.getD q.j default)
  tL : (L.getD q.j default).t = q.t
  tv : (lv q.j).t = q.t
  t1 : 1 ≤ q.t
  htI : (L.getD q.j default).ht = (lv q.j).ht
  wdI : (L.getD q.j default).wd = q.wdI
  capI : V.capOfL L (L.getD q.j default).ht q.wdI = (lv q.j).lv
  leafI : 8 * min (V.occL L (L.getD q.j default).ht q.wdI) q.wdI = (lv q.j).leaf
  levLeaf : q.lev.leafB = (lv q.j).leaf
  levHt : q.lev.ht = (lv q.j).ht
  levLv : q.lev.lv = (lv q.j).lv
  htN : (L.getD (q.j + 1) default).ht = q.ht
  wdN : (L.getD (q.j + 1) default).wd = q.wd
  capN : V.capOfL L q.ht q.wd = (lv (q.j + 1)).lv
  lvN : (lv (q.j + 1)).lv = q.lvN

theorem layEnd_append : ∀ (l₁ l₂ : List V.Item) (a : ℕ), layEnd (l₁ ++ l₂) a = layEnd l₂ (layEnd l₁ a)
  | [], _, _ => rfl
  | it :: its, l₂, a => by
    rw [List.cons_append, layEnd_cons, layEnd_append its l₂, layEnd_cons it its]

theorem rep_cons (n : ℕ) (l : List V.Item) : rep (n + 1) l = l ++ rep n l := by
  simp [rep, List.replicate_succ]

theorem layRounds_eq (g : ℕ) : ∀ ℓ a, QC.layRounds g ℓ a = QC.bl (layItems (rep ℓ [.E 4, .G g, .D 1]) a) ∧
    layEnd (rep ℓ [.E 4, .G g, .D 1]) a = a + 27 * ℓ
  | 0, a => ⟨rfl, rfl⟩
  | ℓ + 1, a => by
    obtain ⟨h1, h2⟩ := layRounds_eq g ℓ (a + 27)
    rw [rep_cons, layItems_append, layEnd_append]
    refine ⟨?_, ?_⟩
    · show QC.layRound g a ++ QC.layRounds g ℓ (a + 27) = _
      rw [h1, QC.bl, QC.bl, List.map_append]
      rfl
    · show layEnd _ (a + 4 * 2 + 10 + 9 * 1) = _
      rw [h2]; ring

theorem layItems_GD_succ (g k b : ℕ) : layItems [.G g, .D (k + 1)] b =
    layItems [.G g, .D k] b ++ layItems [.D 1] (layEnd [.G g, .D k] b) := by
  simp [layItems, layEnd, List.range_succ]

theorem layItems_B_cons (r : List V.Item) (x : ℕ) : layItems (.B :: r) x = [.d x 0] ++ layItems r (x + 9) := rfl
theorem layEnd_B_cons (r : List V.Item) (x : ℕ) : layEnd (.B :: r) x = layEnd r (x + 9) := rfl

/-- **CC's level slots, piece by piece** (the lanes of the pieces as `layEnd`s). -/
theorem MidP.lay_eq (q : MidP) (a : ℕ) : q.lay a =
    QC.bl (layItems q.pre a) ++ ([.c q.ht q.wd] ++ (QC.bl (layItems q.ood (layEnd q.pre a + 4 * 2 ^ q.lvN)) ++
      (QC.bl (layItems [.G q.gQ, .D q.kq] (layEnd q.ood (layEnd q.pre a + 4 * 2 ^ q.lvN))) ++
      (QC.bl (layItems [.D 1] (layEnd [.G q.gQ, .D q.kq] (layEnd q.ood (layEnd q.pre a + 4 * 2 ^ q.lvN)))) ++
      [.o (QC.openRows q.lev q.wdI (layEnd [.D 1] (layEnd [.G q.gQ, .D q.kq]
        (layEnd q.ood (layEnd q.pre a + 4 * 2 ^ q.lvN))) - 4) q.t)])))) := by
  obtain ⟨r1, r2⟩ := layRounds_eq q.g q.ℓ a
  have hpre : layEnd q.pre a = a + 27 * q.ℓ + 2 * q.ℓ := by
    rw [MidP.pre, layEnd_append, r2]; rfl
  have ft : QC.tailOpenAt q.ℓ q.ko q.kq q.lvN (a + 27 * q.ℓ) = layEnd [.D 1] (layEnd [.G q.gQ, .D q.kq]
      (layEnd q.ood (a + 27 * q.ℓ + 2 * q.ℓ + 4 * 2 ^ q.lvN))) := by
    simp only [QC.tailOpenAt, MidP.ood, layEnd]; ring
  rw [hpre, MidP.lay, r1, QC.layTail]
  rw [ft, show [V.Item.G q.gO, .D q.ko, .E 1, .G q.gQ, .D (q.kq + 1)] =
    [V.Item.G q.gO, .D q.ko, .E 1] ++ [.G q.gQ, .D (q.kq + 1)] from rfl, layItems_append, layItems_GD_succ,
    MidP.pre, layItems_append, r2, MidP.ood, layItems_B_cons, layEnd_B_cons]
  simp only [QC.bl, List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]

/-- **CC's level end lane** is the pieces'. -/
theorem MidP.aEnd_eq (q : MidP) (a : ℕ) : q.aEnd a = layEnd [.D 1] (layEnd [.G q.gQ, .D q.kq]
    (layEnd q.ood (layEnd q.pre a + 4 * 2 ^ q.lvN))) + q.t * QC.openStride q.lev := by
  obtain ⟨-, r2⟩ := layRounds_eq q.g q.ℓ a
  rw [MidP.aEnd, MidP.pre, layEnd_append, r2]
  simp only [MidP.ood, layEnd, QC.tailOpenAt]
  ring

/-- **A final level's parameters** (`levelPart` of the last level; CC's `layFin`). -/
structure FinP where
  j : ℕ
  g : ℕ
  ℓ : ℕ
  nf : ℕ
  kq : ℕ
  t : ℕ
  gq : ℕ
  gT : ℕ
  κ : ℕ
  wdI : ℕ
  lev : Level

def FinP.pre (q : FinP) : List V.Item := rep q.ℓ [.E 4, .G q.g, .D 1] ++ [.E q.nf]
def FinP.tl (q : FinP) : List V.Item := rep q.κ (rnd 2 q.gT)
def FinP.items (q : FinP) : List V.Item := q.pre ++ ([.pos q.j q.gq] ++ ([.open q.j] ++ q.tl))
def FinP.lay (q : FinP) (a : ℕ) : List QC.OEv :=
  QC.layFin q.nf q.kq q.t q.κ q.lev q.wdI q.g q.gq q.gT q.ℓ a

structure FinOk (L : List V.Lev) (lv : ℕ → Lv) (q : FinP) : Prop where
  draws : V.Lev.draws (L.getD q.j default) = (lv q.j).d
  kq : q.kq + 1 = (lv q.j).d
  per : 1 ≤ V.Lev.per (L.getD q.j default)
  tL : (L.getD q.j default).t = q.t
  tv : (lv q.j).t = q.t
  t1 : 1 ≤ q.t
  htI : (L.getD q.j default).ht = (lv q.j).ht
  wdI : (L.getD q.j default).wd = q.wdI
  capI : V.capOfL L (L.getD q.j default).ht q.wdI = (lv q.j).lv
  leafI : 8 * min (V.occL L (L.getD q.j default).ht q.wdI) q.wdI = (lv q.j).leaf
  levLeaf : q.lev.leafB = (lv q.j).leaf
  levHt : q.lev.ht = (lv q.j).ht
  levLv : q.lev.lv = (lv q.j).lv

theorem FinP.lay_eq (q : FinP) (a : ℕ) : q.lay a =
    QC.bl (layItems q.pre a) ++ (QC.bl (layItems [.G q.gq, .D q.kq] (layEnd q.pre a)) ++
      ([.o (QC.openRows q.lev q.wdI (layEnd [.G q.gq, .D q.kq] (layEnd q.pre a) - 4) q.t)] ++
      QC.bl (layItems q.tl (layEnd [.G q.gq, .D q.kq] (layEnd q.pre a) + q.t * QC.openStride q.lev)))) := by
  obtain ⟨r1, r2⟩ := layRounds_eq q.g q.ℓ a
  have hpre : layEnd q.pre a = a + 27 * q.ℓ + 2 * q.nf := by
    rw [FinP.pre, layEnd_append, r2]; rfl
  have f1 : QC.finOpenAt q.nf q.kq q.ℓ a = layEnd [.G q.gq, .D q.kq] (a + 27 * q.ℓ + 2 * q.nf) := by
    simp only [QC.finOpenAt, layEnd]
  have f2 : layEnd [.E q.nf] (a + 27 * q.ℓ) = a + 27 * q.ℓ + 2 * q.nf := by simp only [layEnd]
  rw [hpre, FinP.lay, QC.layFin, r1, f1, show [V.Item.E q.nf, .G q.gq, .D q.kq] =
    [V.Item.E q.nf] ++ [.G q.gq, .D q.kq] from rfl, layItems_append, f2, FinP.pre, layItems_append, r2]
  simp only [QC.bl, List.map_append, List.append_assoc, FinP.tl]

section Level

variable {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem}

set_option hygiene false in
local notation "τP" => decode6 P ws
set_option hygiene false in
local notation "πP" => reassemble6 P (decode6 P ws)

variable (hS : streamOkL6 P = true) (hw : hashedLen6 P ≤ 8 * ws.length)
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P ws)

theorem capsSh_plain {its : List V.Item} (h : ∀ it ∈ its, plainB it = true) : its.flatMap (capSh L) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro it hit
  have := h it hit
  cases it <;> simp_all [plainB, capSh]

theorem caps_at {l : List (ℕ × ℕ × ℕ)} {j : ℕ} {x : ℕ × ℕ} (h : (l.map (·.2))[j]? = some x) :
    ∃ o, l[j]? = some (o, x) := by
  rw [List.getElem?_map] at h
  cases hl : l[j]? with
  | none => rw [hl] at h; simp at h
  | some y => rw [hl] at h; simp at h; exact ⟨y.1, by rw [← h]⟩

theorem pre_plain (ℓ g e : ℕ) : ∀ it ∈ rep ℓ [V.Item.E 4, .G g, .D 1] ++ [.E e], plainB it = true := by
  intro it hit
  rcases List.mem_append.mp hit with hit | hit
  · simp only [rep, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨_, ⟨-, rfl⟩, hx⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; subst hit; rfl

include hS hw hM hpow in
/-- **One mid level** (generic): V1's values of `q.items` match CC's slots `q.lay (laneW w)`, the simulation
reaches the level's end lane `q.aEnd`, and the level's cap shape is recorded. -/
theorem simO_mid (q : MidP) (hq : MidOk L lv q) {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s (q.items.flatMap (itOfs lv) ++ R))
    (hc : (s.1.caps.map (·.2))[q.j]? = some ((L.getD q.j default).ht, (L.getD q.j default).wd)) :
    ∃ w', SimO P ws lv L M q.items w s R (q.lay (laneW P w)) w' ∧ laneW P w' = q.aEnd (laneW P w) ∧
      (nxt πP L τP q.items s).1.caps.map (·.2) = s.1.caps.map (·.2) ++ [(q.ht, q.wd)] := by
  have hpp : ∀ it ∈ q.pre, plainB it = true := pre_plain q.ℓ q.g q.ℓ
  have hop : ∀ it ∈ q.ood, plainB it = true := by
    intro it hit; simp only [MidP.ood, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl | rfl <;> rfl
  have e1 : q.items.flatMap (itOfs lv) ++ R = q.pre.flatMap (itOfs lv) ++
      (([V.Item.cap (q.j + 1)] ++ (q.ood ++ ([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j])))).flatMap (itOfs lv) ++ R) := by
    simp [MidP.items]
  rw [e1] at h
  obtain ⟨S1, l1⟩ := simO_plain hS hw hM hpow (L := L) q.pre hpp h
  have h1 := S1.1
  rw [show ([V.Item.cap (q.j + 1)] ++ (q.ood ++ ([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j])))).flatMap (itOfs lv) ++ R =
    itOfs lv (.cap (q.j + 1)) ++ ((q.ood ++ ([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j]))).flatMap (itOfs lv) ++ R)
    by simp] at h1
  obtain ⟨S2, q2, d2⟩ := simO_cap (M := M) (q.j + 1) (by rw [hq.htN, hq.wdN]; exact hq.capN) h1
  have h2 := S2.1
  rw [show (q.ood ++ ([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j]))).flatMap (itOfs lv) ++ R =
    q.ood.flatMap (itOfs lv) ++ (([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j])).flatMap (itOfs lv) ++ R)
    by simp] at h2
  obtain ⟨S3, l3⟩ := simO_plain hS hw hM hpow (L := L) q.ood hop h2
  have h3 := S3.1
  rw [show ([V.Item.pos q.j q.gQ] ++ ([V.Item.D 1] ++ [V.Item.open q.j])).flatMap (itOfs lv) ++ R =
    itOfs lv (.pos q.j q.gQ) ++ (([V.Item.D 1] ++ [V.Item.open q.j]).flatMap (itOfs lv) ++ R) by simp] at h3
  have ekq : (lv q.j).d - 1 = q.kq := by have := hq.kq; omega
  obtain ⟨S4, l4⟩ := simO_pos (L := L) hS hw hM hpow q.j q.gQ hq.draws hq.per (by rw [hq.tL]; exact hq.t1) h3
  rw [ekq] at S4 l4
  have h4 := S4.1
  rw [show ([V.Item.D 1] ++ [V.Item.open q.j]).flatMap (itOfs lv) ++ R =
    [V.Item.D 1].flatMap (itOfs lv) ++ ([V.Item.open q.j].flatMap (itOfs lv) ++ R) by simp] at h4
  obtain ⟨S5, l5⟩ := simO_plain hS hw hM hpow (L := L) [V.Item.D 1] (by intro it hit; simp at hit; subst hit; rfl) h4
  have h5 := S5.1
  rw [show [V.Item.open q.j].flatMap (itOfs lv) ++ R = itOfs lv (.open q.j) ++ R by simp] at h5
  -- the opening: positions and cap
  have hps : (nxt πP L τP [V.Item.D 1] (nxt πP L τP [V.Item.pos q.j q.gQ] (nxt πP L τP q.ood
      (nxt πP L τP [.cap (q.j + 1)] (nxt πP L τP q.pre s))))).1.ps.length = (lv q.j).t := by
    rw [nxt_one]
    show (V.Prims.rep (PA πP L τP) ((PA πP L τP).draw V.tt V.keepPs) 1 _).1.ps.length = _
    rw [rep_ps_keep, (item_pos πP L τP (i := q.j) (g := q.gQ) hq.per (by rw [hq.tL]; exact hq.t1) _).2.2.1,
      posAll_length, hq.tL, hq.tv]
  have hcs : (nxt πP L τP [V.Item.D 1] (nxt πP L τP [V.Item.pos q.j q.gQ] (nxt πP L τP q.ood
      (nxt πP L τP [.cap (q.j + 1)] (nxt πP L τP q.pre s))))).1.caps.map (·.2) =
      s.1.caps.map (·.2) ++ [(q.ht, q.wd)] := by
    have e := walk_capsSh πP L τP (q.pre ++ ([V.Item.cap (q.j + 1)] ++ (q.ood ++ ([V.Item.pos q.j q.gQ] ++ [V.Item.D 1])))) s
    rw [nxt_append, nxt_append, nxt_append, nxt_append] at e
    rw [e, List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      capsSh_plain hpp, capsSh_plain hop]
    simp [capSh, ← hq.htN, ← hq.wdN]
  have hcj : ∃ o, (nxt πP L τP [V.Item.D 1] (nxt πP L τP [V.Item.pos q.j q.gQ] (nxt πP L τP q.ood
      (nxt πP L τP [.cap (q.j + 1)] (nxt πP L τP q.pre s))))).1.caps[q.j]? =
      some (o, (L.getD q.j default).ht, q.wdI) := by
    apply caps_at
    rw [hcs, List.getElem?_append_left (by
      have := (List.getElem?_eq_some_iff.mp hc).1; exact this), hc, hq.wdI]
  obtain ⟨o, hcj⟩ := hcj
  obtain ⟨w6, S6, l6⟩ := simO_open hS hw hM (L := L) (lev := q.lev) q.j h5 hps hcj hq.htI hq.capI hq.leafI
    ⟨hq.levLeaf, hq.levHt, hq.levLv⟩
  have T := simO_append S1 (simO_append S2 (simO_append S3 (simO_append S4 (simO_append S5 S6))))
  have c2 : laneW P (walk lv (walk lv w (q.pre.flatMap (itOfs lv))).2 ([V.Item.cap (q.j + 1)].flatMap (itOfs lv))).2 =
      laneW P (walk lv w (q.pre.flatMap (itOfs lv))).2 + 4 * 2 ^ q.lvN := by
    have h8 := S1.1.2.2.2.1
    simp only [laneW]
    rw [q2, d2, ← hq.lvN]
    omega
  refine ⟨w6, simO_eq ?_ T, ?_, ?_⟩
  · rw [q.lay_eq, l1, ← c2, l3, l4, l5, hq.htN, hq.wdN, hq.tv]
  · rw [l6, q.aEnd_eq, l1, ← c2, l3, l4, l5, hq.tv]
  · have e := walk_capsSh πP L τP q.items s
    rw [e]
    simp [MidP.items, List.flatMap_append, capsSh_plain hpp, capsSh_plain hop, capSh, ← hq.htN, ← hq.wdN]

include hS hw hM hpow in
/-- **The final level** (generic). -/
theorem simO_fin (q : FinP) (hq : FinOk L lv q) {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s (q.items.flatMap (itOfs lv) ++ R))
    (hc : (s.1.caps.map (·.2))[q.j]? = some ((L.getD q.j default).ht, (L.getD q.j default).wd)) :
    ∃ w', SimO P ws lv L M q.items w s R (q.lay (laneW P w)) w' := by
  have hpp : ∀ it ∈ q.pre, plainB it = true := pre_plain q.ℓ q.g q.nf
  have htl : ∀ it ∈ q.tl, plainB it = true := by
    intro it hit
    simp only [FinP.tl, rep, rnd, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨_, ⟨-, rfl⟩, hx⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  have e1 : q.items.flatMap (itOfs lv) ++ R = q.pre.flatMap (itOfs lv) ++
      (([V.Item.pos q.j q.gq] ++ ([V.Item.open q.j] ++ q.tl)).flatMap (itOfs lv) ++ R) := by
    simp [FinP.items]
  rw [e1] at h
  obtain ⟨S1, l1⟩ := simO_plain hS hw hM hpow (L := L) q.pre hpp h
  have h1 := S1.1
  rw [show ([V.Item.pos q.j q.gq] ++ ([V.Item.open q.j] ++ q.tl)).flatMap (itOfs lv) ++ R =
    itOfs lv (.pos q.j q.gq) ++ (([V.Item.open q.j] ++ q.tl).flatMap (itOfs lv) ++ R) by simp] at h1
  have ekq : (lv q.j).d - 1 = q.kq := by have := hq.kq; omega
  obtain ⟨S2, l2⟩ := simO_pos (L := L) hS hw hM hpow q.j q.gq hq.draws hq.per (by rw [hq.tL]; exact hq.t1) h1
  rw [ekq] at S2 l2
  have h2 := S2.1
  rw [show ([V.Item.open q.j] ++ q.tl).flatMap (itOfs lv) ++ R = itOfs lv (.open q.j) ++ (q.tl.flatMap (itOfs lv) ++ R)
    by simp] at h2
  have hps : (nxt πP L τP [V.Item.pos q.j q.gq] (nxt πP L τP q.pre s)).1.ps.length = (lv q.j).t := by
    rw [(item_pos πP L τP (i := q.j) (g := q.gq) hq.per (by rw [hq.tL]; exact hq.t1) _).2.2.1,
      posAll_length, hq.tL, hq.tv]
  have hcj : ∃ o, (nxt πP L τP [V.Item.pos q.j q.gq] (nxt πP L τP q.pre s)).1.caps[q.j]? =
      some (o, (L.getD q.j default).ht, q.wdI) := by
    apply caps_at
    have e := walk_capsSh πP L τP (q.pre ++ [V.Item.pos q.j q.gq]) s
    rw [nxt_append] at e
    rw [e, List.flatMap_append, capsSh_plain hpp]
    simp only [capSh, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
    rw [hc, hq.wdI]
  obtain ⟨o, hcj⟩ := hcj
  obtain ⟨w3, S3, l3⟩ := simO_open hS hw hM (L := L) (lev := q.lev) q.j h2 hps hcj hq.htI hq.capI hq.leafI
    ⟨hq.levLeaf, hq.levHt, hq.levLv⟩
  obtain ⟨S4, l4⟩ := simO_plain hS hw hM hpow (L := L) q.tl htl S3.1
  have T := simO_append S1 (simO_append S2 (simO_append S3 S4))
  refine ⟨_, simO_eq ?_ T⟩
  rw [q.lay_eq, l1, l2, ← hq.tv, ← l3]

end Level

/-! ## At `P18` (the instances, last) -/

/-- Mid level `j`'s parameters at `P18`. -/
def midP18 (j : ℕ) : MidP where
  j := j
  g := (P18.lvl j).gFold
  ℓ := (P18.lvl j).fold
  ko := P18.nu (j + 1) - 1
  kq := (lvOf P18 j).d - 1
  t := (lvOf P18 j).t
  gO := (P18.lvl (j + 1)).gOod
  gQ := (P18.lvl j).gQuery
  ht := (P18.levs.getD (j + 1) default).ht
  wd := (P18.levs.getD (j + 1) default).wd
  lvN := (P18.lvl (j + 1)).lv
  wdI := QC.wdOf j
  lev := P18.lvl j

/-- The final level's index and parameters at `P18`. -/
def jF18 : ℕ := P18.levels.length - 1

def finP18 : FinP where
  j := jF18
  g := (P18.lvl jF18).gFold
  ℓ := (P18.lvl jF18).fold
  nf := P18.finalLen
  kq := (lvOf P18 jF18).d - 1
  t := (lvOf P18 jF18).t
  gq := (P18.lvl jF18).gQuery
  gT := P18.gr.tail
  κ := P18.tail
  wdI := QC.wdOf jF18
  lev := P18.lvl jF18

theorem midOk18 (j : ℕ) (hj : j < jF18) : MidOk P18.levs (lvOf P18) (midP18 j) := by
  have hj' : j < 4 := hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem finOk18 : FinOk P18.levs (lvOf P18) finP18 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem levelPart_mid18 (j : ℕ) (hj : j < jF18) : P18.levelPart j = (midP18 j).items := by
  rw [lp_mid hj]
  simp [Amid, MidP.items, MidP.pre, MidP.ood, midP18]

theorem levelPart_fin18 : P18.levelPart jF18 = finP18.items := by
  rw [show jF18 = 4 from rfl, lp_fin]
  simp [Afin, Tfin, FinP.items, FinP.pre, FinP.tl, finP18, jF18]
  rfl

/-- The opening's lanes: after the ring part, then each level's end. -/
def aO : ℕ → ℕ
  | 0 => layEnd P18.ringPart aRing
  | j + 1 => (midP18 j).aEnd (aO j)

/-- **The opening's slots at `P18`** (CC's `layRounds`/`layTail` per mid level, `layFin`). -/
def layO : List QC.OEv :=
  (midP18 0).lay (aO 0) ++ ((midP18 1).lay (aO 1) ++ ((midP18 2).lay (aO 2) ++ ((midP18 3).lay (aO 3) ++
    finP18.lay (aO jF18))))

theorem inv_app_nil {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {w : WS6} {s : AS} {R : List It}
    (h : Inv P ws lv w s R) : Inv P ws lv w s (R ++ []) := by rw [List.append_nil]; exact h

theorem simO_app_nil {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem} {its : List V.Item}
    {w w' : WS6} {s : AS} {R : List It} {lay : List QC.OEv} (h : SimO P ws lv L M its w s R lay w') :
    SimO P ws lv L M its w s (R ++ []) lay w' := by rw [List.append_nil]; exact h

theorem simO_R {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem} {its : List V.Item}
    {w w' : WS6} {s : AS} {R R' : List It} {lay : List QC.OEv} (hR : R = R') (h : SimO P ws lv L M its w s R lay w') :
    SimO P ws lv L M its w s R' lay w' := hR ▸ h

theorem simO_nil {P : List PE6} {ws : List Word} {lv : ℕ → Lv} {L : List V.Lev} {M : Mem} {w : WS6} {s : AS}
    {R : List It} (h : Inv P ws lv w s R) : SimO P ws lv L M [] w s R [] w :=
  ⟨h, List.Forall₂.nil, fun _ _ h ↦ absurd h List.not_mem_nil⟩

section Slots

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Mem}
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P6 ws)

include hw hM hpow in
/-- **The opening's slot facts** (`htail_of_cc`'s `hpW`, `heW` at `layW = layO`). -/
theorem open_slots : QC.PowLayO M layO ∧ QC.OEvMatch M layO ((segO ws).map toEv) := by
  have hS := streamOkP18
  obtain ⟨-, -, -, w, hI, hL⟩ := split6 hw hM hpow
  rw [its18, List.flatMap_append] at hI
  -- the ring part
  obtain ⟨⟨I0, -, -⟩, l0⟩ := simO_plain hS hw hM hpow (L := P18.levs) (M := M) P18.ringPart
    (by intro it hit; simp only [Shape.ringPart, List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> rfl) hI
  rw [hL] at l0
  have hst : nxt (reassemble6 P6 (decode6 P6 ws)) P18.levs (decode6 P6 ws) P18.ringPart (stAt ws preR) =
      stAt ws preO := (stAt_append ws preR _).symm
  rw [hst] at I0
  have hop : P18.openPart = (midP18 0).items ++ ((midP18 1).items ++ ((midP18 2).items ++
      ((midP18 3).items ++ finP18.items))) := by
    rw [openPart_eq, levelPart_mid18 0 (by decide), levelPart_mid18 1 (by decide), levelPart_mid18 2 (by decide),
      levelPart_mid18 3 (by decide), show (4 : ℕ) = jF18 from rfl, levelPart_fin18]
  rw [hop] at I0
  simp only [List.flatMap_append] at I0
  have c0 : ((stAt ws preO).1.caps.map (·.2)) = [((P18.levs.getD 0 default).ht, (P18.levs.getD 0 default).wd)] := by
    rw [stAt, walk_capsSh]
    have hp : ∀ it ∈ P18.treePart ++ P18.spongePart ++ (P18.subT.typed ++ P18.subT.bus) ++ P18.ringPart,
        plainB it = true := by
      intro it hit
      rcases List.mem_append.mp hit with hit | hit
      · exact List.all_eq_true.mp plain18 it hit
      · simp only [Shape.ringPart, List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> rfl
    have e : preO = P18.commitPart ++ (P18.treePart ++ P18.spongePart ++ (P18.subT.typed ++ P18.subT.bus) ++
        P18.ringPart) := by
      simp only [preO, preR, preY, preS, preT, List.append_assoc]
    rw [e, List.flatMap_append, capsSh_plain hp, commitPart_eq]
    rfl
  obtain ⟨w1, T0, a1, c1⟩ := simO_mid hS hw hM hpow (midP18 0) (midOk18 0 (by decide)) I0 (by rw [c0]; rfl)
  obtain ⟨w2, T1, a2, c2⟩ := simO_mid hS hw hM hpow (midP18 1) (midOk18 1 (by decide)) T0.1
    (by rw [c1, c0]; rfl)
  obtain ⟨w3, T2, a3, c3⟩ := simO_mid hS hw hM hpow (midP18 2) (midOk18 2 (by decide)) T1.1
    (by rw [c2, c1, c0]; rfl)
  obtain ⟨w4, T3, a4, c4⟩ := simO_mid hS hw hM hpow (midP18 3) (midOk18 3 (by decide)) T2.1
    (by rw [c3, c2, c1, c0]; rfl)
  obtain ⟨w5, T4⟩ := simO_fin hS hw hM hpow finP18 finOk18 (R := []) (inv_app_nil T3.1)
    (by rw [c4, c3, c2, c1, c0]; rfl)
  have T0' := simO_R (R' := ((midP18 1).items ++ ((midP18 2).items ++ ((midP18 3).items ++ finP18.items))).flatMap
    (itOfs (lvOf P18)) ++ []) (by simp only [List.flatMap_append, List.append_nil]) T0
  have T1' := simO_R (R' := ((midP18 2).items ++ ((midP18 3).items ++ finP18.items)).flatMap
    (itOfs (lvOf P18)) ++ []) (by simp only [List.flatMap_append, List.append_nil]) T1
  have T2' := simO_R (R' := ((midP18 3).items ++ finP18.items).flatMap (itOfs (lvOf P18)) ++ [])
    (by simp only [List.flatMap_append, List.append_nil]) T2
  have T := simO_append T0' (simO_append T1' (simO_append T2' (simO_append (simO_app_nil T3) T4)))
  rw [← l0] at T a1
  rw [show layEnd P18.ringPart (partLane preR) = aO 0 from rfl] at T a1
  rw [a1, show (midP18 0).aEnd (aO 0) = aO 1 from rfl] at T a2
  rw [a2, show (midP18 1).aEnd (aO 1) = aO 2 from rfl] at T a3
  rw [a3, show (midP18 2).aEnd (aO 2) = aO 3 from rfl] at T a4
  rw [a4, show (midP18 3).aEnd (aO 3) = aO jF18 from rfl] at T
  obtain ⟨-, e, p⟩ := T
  refine ⟨p, ?_⟩
  unfold segO segAt
  rw [hop]
  exact e

end Slots

end Lvm6.Node.Split
