-- New for lvm6 (WP N4-split, extra targets for N4-tail). V1's side of the opening's `(i, ps)` agreement
-- (`RowsF F18 [] (segO ws)`) and the ring segment's slot facts against CC's `layRing6`, in the form
-- `htail_of_cc` consumes.
import Lvm6NodeSplit
import Lvm6NodeTailO

/-!
# V1's openings carry `F18`; the ring slots (WP N4-split, for N4-tail)

* **`ring_slots`**: `PowLayO`, `NoRows`, `OEvMatch` of `segR ws` against `layRing6 17 aRing`
  (`aRing = partLane preR`; the ring part `B, G(17), D(32)` is plain, `simPart`).
* **`rowsF_segO`**: `RowsF F18 [] (segO ws)` for every `ws`. V1's `j`-th opening value is `.rows j ps r`:
  `j` because every level reads its cap before its opening (`caps` has `j + 1` entries then), `ps` because
  V1's driver positions after `pos j g` are `posAll` of the group's draws (CA2's `posAll_snoc`), which is
  W1's `posE2` (`qPos`/`fPos`) of the same draws' values (`e2Nat_chal`: `e2Nat (e2OfE (chalOf a)) = drawN a`).
  The draws are the last `kq + 2` (mid levels: the group and `λ`) or `3` (final) samples before the opening
  (`lastS_grp`).
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node
open Lvm.QLink (lw laneK slenS)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop LeanVM.Parameters

set_option hygiene false in
local notation "τW" => decode6 P6 ws
set_option hygiene false in
local notation "πW" => reassemble6 P6 (decode6 P6 ws)

/-! ## The ring slots -/

/-- The ring part's first lane. -/
def aRing : ℕ := partLane preR

theorem bl_ring (a : ℕ) : QC.layRing6 17 a = QC.bl (layItems P18.ringPart a) := rfl

theorem oevMatch_bl {M : Mem} {l : List LEv} {evs : List Ev} (h : EvMatch M l evs) :
    QC.OEvMatch M (QC.bl l) evs := by
  unfold QC.OEvMatch QC.bl
  rw [List.forall₂_map_left_iff]
  exact h

theorem powLayO_bl {M : Mem} {l : List LEv} (h : PowLay M l) : QC.PowLayO M (QC.bl l) := by
  intro a g hm
  unfold QC.bl at hm
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
  cases he
  exact h a g hx

section Ring

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Mem}
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P6 ws)

include hw hM hpow in
/-- **The ring segment's slot facts** (`htail_of_cc`'s `hpR`, `hnR`, `heR` at `aR = aRing`). -/
theorem ring_slots : QC.PowLayO M (QC.layRing6 17 aRing) ∧ NoRows (segR ws) ∧
    QC.OEvMatch M (QC.layRing6 17 aRing) ((segR ws).map toEv) := by
  obtain ⟨-, -, -, w, hI, hL⟩ := split6 hw hM hpow
  rw [its18, List.flatMap_append] at hI
  obtain ⟨-, e1, n1, p1, -, -, -⟩ := simPart (lvOf P18) P18.levs streamOkP18 hw hM hpow P18.ringPart
    (by intro it hit; simp only [Shape.ringPart, List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl <;> rfl) hI
  rw [hL] at e1 p1
  exact ⟨by rw [bl_ring]; exact powLayO_bl p1, n1, by rw [bl_ring]; exact oevMatch_bl e1⟩

end Ring

/-! ## `RowsF` along a list -/

theorem rowsF_append {F : List Ev → ℕ × List ℕ} {E : List Ev} {a b : List V.Val} (ha : RowsF F E a)
    (hb : RowsF F (E ++ a.map toEv) b) : RowsF F E (a ++ b) := by
  intro pre i ps r post he
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, hb'⟩ | ⟨c', rfl, hc'⟩
  · rw [hb a' i ps r post hb', List.map_append, List.append_assoc]
  · cases c' with
    | nil =>
      simp only [List.nil_append] at hc'
      rw [← hc'] at hb
      have := hb [] i ps r post rfl
      simpa using this
    | cons x c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      exact ha pre i ps r c'' rfl

theorem rowsF_noRows {F : List Ev → ℕ × List ℕ} {E : List Ev} {a : List V.Val} (h : NoRows a) : RowsF F E a := by
  intro pre i ps r post he
  exact absurd rfl (h (V.Val.rows i ps r) (by rw [he]; simp) i ps r)

theorem qcount_noRows {a : List V.Val} (h : NoRows a) : qcount (a.map toEv) = 0 := by
  simp only [qcount, List.countP_eq_zero, List.mem_map]
  rintro e ⟨v, hv, rfl⟩
  cases v with
  | rows i ps r => exact absurd rfl (h _ hv i ps r)
  | _ => simp [toEv, isQ]

/-! ## Caps and values of the items without openings -/

/-- The caps an item reads. -/
def capsN : V.Item → ℕ
  | .cap _ => 1
  | _ => 0

/-- Items without openings or positions. -/
def pcB : V.Item → Bool
  | .open _ | .pos _ _ => false
  | _ => true

section Caps

variable (π : ByteArray) (L : List V.Lev) (tr : Trace)

theorem rep_caps {f : AS → AS} (hf : ∀ s, (f s).1.caps = s.1.caps) :
    ∀ m s, (V.Prims.rep (PA π L tr) f m s).1.caps = s.1.caps
  | 0, _ => rfl
  | m + 1, s => (rep_caps hf m (f s)).trans (hf s)

theorem posRest_caps (ht : ℕ) : ∀ cs s, (V.Prims.posRest (PA π L tr) ht cs s).1.caps = s.1.caps
  | [], _ => rfl
  | _ :: cs, s => posRest_caps ht cs _

theorem item_caps (it : V.Item) (s : AS) :
    (nxt π L tr [it] s).1.caps.length = s.1.caps.length + capsN it := by
  rw [nxt_one]
  cases it with
  | E k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).rd 16) k s).1.caps.length = _
    rw [rep_caps π L tr (f := (PA π L tr).rd 16) (fun _ ↦ rfl)]; rfl
  | K k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).rd 8) k s).1.caps.length = _
    rw [rep_caps π L tr (f := (PA π L tr).rd 8) (fun _ ↦ rfl)]; rfl
  | cap i => simp [V.Prims.item, PA, aCap, capsN]
  | G g => rfl
  | D k =>
    show (V.Prims.rep (PA π L tr) ((PA π L tr).draw V.tt V.keepPs) k s).1.caps.length = _
    rw [rep_caps π L tr (f := (PA π L tr).draw V.tt V.keepPs) (fun _ ↦ rfl)]; rfl
  | B => rfl
  | pos i g =>
    show (V.Prims.posRest (PA π L tr) _ _ _).1.caps.length = _
    rw [posRest_caps]; rfl
  | «open» i =>
    show ((PA π L tr).opn i s).1.caps.length = _
    simp only [PA]
    split <;> rfl

theorem walk_caps : ∀ (its : List V.Item) (s : AS),
    (nxt π L tr its s).1.caps.length = s.1.caps.length + (its.map capsN).sum
  | [], _ => rfl
  | it :: its, s => by
    rw [nxt_cons, walk_caps its, item_caps, List.map_cons, List.sum_cons]; omega

theorem noRows_pc : ∀ (its : List V.Item), (∀ it ∈ its, pcB it = true) → ∀ s, NoRows (segV π L tr its s)
  | [], _, s => by intro v hv; exact absurd hv (by simp [segV, clr, V.Prims.walk, PA])
  | it :: its, h, s => by
    rw [segV_cons]
    intro v hv i ps r
    rcases List.mem_append.mp hv with hv | hv
    · have hp := h it List.mem_cons_self
      cases it with
      | E k => rw [(item_E π L tr k s).1] at hv; simp only [List.mem_map] at hv
               obtain ⟨_, _, rfl⟩ := hv; simp [V.NV.val]
      | K k => rw [(item_K π L tr k s).1] at hv; simp only [List.mem_map] at hv
               obtain ⟨_, _, rfl⟩ := hv; simp [V.NV.val]
      | D k => rw [(item_D π L tr k s).1] at hv; simp only [List.mem_map] at hv
               obtain ⟨_, _, rfl⟩ := hv; simp [V.NV.val]
      | G g => rw [(item_G π L tr g s).1] at hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
               rcases hv with rfl | rfl <;> simp [V.NV.val]
      | B => rw [(item_B π L tr s).1] at hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
             subst hv; simp [V.NV.val]
      | cap j => rw [(item_cap π L tr j s).1] at hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                 subst hv; simp
      | pos _ _ => simp [pcB] at hp
      | «open» _ => simp [pcB] at hp
    · exact noRows_pc its (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) _ v hv i ps r

/-! ## A position group and an opening -/

/-- **The further draws of a position group** on the pure driver (CA2's `posRest_core` without the run). -/
theorem posRest_PA {ht t p i0 : ℕ} (hp : 128 / ht = p) (hp1 : 1 ≤ p) :
    ∀ (m j : ℕ) (s : AS), (∀ x < m, (j + x) * p < t) → s.2 = i0 + j →
      s.1.ps = posAll tr i0 ht (min t (j * p)) →
      (V.Prims.posRest (PA π L tr) ht ((List.range' j m).map (cntf p t)) s).2 = i0 + j + m ∧
      (V.Prims.posRest (PA π L tr) ht ((List.range' j m).map (cntf p t)) s).1.ps =
        posAll tr i0 ht (min t ((j + m) * p)) ∧
      (V.Prims.posRest (PA π L tr) ht ((List.range' j m).map (cntf p t)) s).1.acc =
        ((List.range m).map fun x ↦ V.NV.draw (aOf tr (i0 + j + x))).reverse ++ s.1.acc
  | 0, j, s, _, h2, hps =>
    ⟨by show s.2 = _; omega, by show s.1.ps = _; simpa using hps, by show s.1.acc = _; simp⟩
  | m + 1, j, s, hd, h2, hps => by
    have hs : V.Prims.posRest (PA π L tr) ht ((List.range' j (m + 1)).map (cntf p t)) s =
        V.Prims.posRest (PA π L tr) ht ((List.range' (j + 1) m).map (cntf p t))
          (aDraw (V.addPs ht (cntf p t j)) (aOf tr s.2) s.1, s.2 + 1) := by
      rw [List.range'_succ]; rfl
    have hps' : (aDraw (V.addPs ht (cntf p t j)) (aOf tr s.2) s.1).ps = posAll tr i0 ht (min t ((j + 1) * p)) := by
      simp only [aDraw, V.addPs, hps, cntf, h2]
      subst hp
      exact posAll_snoc tr i0 ht t j hp1 (by have := hd 0 (by omega); simpa using this)
    obtain ⟨e1, e2, e3⟩ := posRest_PA hp hp1 m (j + 1)
      (aDraw (V.addPs ht (cntf p t j)) (aOf tr s.2) s.1, s.2 + 1) (fun x hx ↦ by
      have := hd (x + 1) (by omega); rwa [show j + (x + 1) = j + 1 + x by omega] at this)
      (by show s.2 + 1 = i0 + (j + 1); omega) hps'
    rw [hs]
    refine ⟨by rw [e1]; omega, by rw [e2, show j + 1 + m = j + (m + 1) by omega], ?_⟩
    rw [e3]
    simp only [aDraw, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons,
      List.append_assoc, h2, Nat.add_zero, List.singleton_append]
    congr 2
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    congr 2
    omega

/-- **A position group** `pos i g` of a level with `d` draws (`p = ⌊128/ht⌋` positions each, `t` in all):
the nonce, `d` draws, and the positions `posAll` of those draws. -/
theorem item_pos {i g : ℕ} (hp1 : 1 ≤ V.Lev.per (L.getD i default)) (ht1 : 1 ≤ (L.getD i default).t) (s : AS) :
    segV π L tr [.pos i g] s = V.NV.val π (.rd s.1.off 8) ::
        (List.range (V.Lev.draws (L.getD i default))).map (fun x ↦ V.NV.val π (.draw (aOf tr (s.2 + x)))) ∧
      (nxt π L tr [.pos i g] s).2 = s.2 + V.Lev.draws (L.getD i default) ∧
      (nxt π L tr [.pos i g] s).1.ps = posAll tr s.2 (L.getD i default).ht (L.getD i default).t ∧
      (nxt π L tr [.pos i g] s).1.caps = s.1.caps := by
  generalize hl : L.getD i default = lev at hp1 ht1
  have hd1 : 1 ≤ V.Lev.draws lev := le_max_left _ _
  have hd : V.Lev.draws lev = (lev.t + lev.per - 1) / lev.per := by
    have : 1 ≤ (lev.t + lev.per - 1) / lev.per := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    simp only [V.Lev.draws]; omega
  obtain ⟨n, hn⟩ : ∃ n, V.Lev.draws lev = n + 1 := ⟨V.Lev.draws lev - 1, by omega⟩
  have hcn : V.Lev.cnts lev = cntf lev.per lev.t 0 :: (List.range' 1 n).map (cntf lev.per lev.t) := by
    simp only [V.Lev.cnts, hn, List.range_succ_eq_map, List.map_cons, List.map_map, List.range'_eq_map_range]
    refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
    apply List.map_congr_left
    intro x _
    simp only [Function.comp, cntf, Nat.succ_eq_add_one]
    rw [Nat.add_comm x 1]
  have hall : ∀ x < n + 1, x * lev.per < lev.t := fun x hx ↦
    lt_t_of_lt_d hp1 (by rw [← hd, hn]; exact hx)
  have key : ∀ t0 : AS, V.Prims.item (PA π L tr) L (.pos i g) t0 =
      V.Prims.posRest (PA π L tr) lev.ht ((List.range' 1 n).map (cntf lev.per lev.t))
        (aDraw (V.addPs lev.ht (cntf lev.per lev.t 0)) (aOf tr t0.2) (aRd π 8 { t0.1 with ps := [] }), t0.2 + 1) := by
    intro t0
    show V.Prims.posRest (PA π L tr) (L.getD i default).ht (V.Lev.cnts (L.getD i default)).tail _ = _
    rw [hl, hcn]
    rfl
  have hper : 128 / lev.ht = lev.per := rfl
  have hps0 : ∀ t0 : AS, (aDraw (V.addPs lev.ht (cntf lev.per lev.t 0)) (aOf tr t0.2)
      (aRd π 8 { t0.1 with ps := [] })).ps = posAll tr t0.2 lev.ht (min lev.t (1 * lev.per)) := by
    intro t0
    have := posAll_snoc tr t0.2 lev.ht lev.t 0 (by rw [hper]; exact hp1) (by rw [hper]; omega)
    rw [hper] at this
    simp only [Nat.zero_mul, Nat.min_zero, Nat.add_zero, Nat.zero_add] at this
    simp only [aDraw, aRd, V.addPs, cntf, Nat.zero_mul, Nat.sub_zero, List.nil_append]
    rw [← this]
    simp [posAll]
  obtain ⟨a1, a2, a3⟩ := posRest_PA π L tr (i0 := (clr s).2) hper hp1 n 1
    (aDraw (V.addPs lev.ht (cntf lev.per lev.t 0)) (aOf tr (clr s).2) (aRd π 8 { (clr s).1 with ps := [] }),
      (clr s).2 + 1) (fun x hx ↦ hall _ (by omega)) rfl (hps0 (clr s))
  obtain ⟨b1, b2, -⟩ := posRest_PA π L tr (i0 := s.2) hper hp1 n 1
    (aDraw (V.addPs lev.ht (cntf lev.per lev.t 0)) (aOf tr s.2) (aRd π 8 { s.1 with ps := [] }), s.2 + 1)
    (fun x hx ↦ hall _ (by omega)) rfl (hps0 s)
  rw [hn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [segV_one, key, a3]
    simp only [aDraw, aRd, clr, List.append_nil, List.map_append, List.map_reverse, List.reverse_append,
      List.reverse_reverse, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.range_succ_eq_map, List.map_map, Nat.add_zero, List.singleton_append, List.cons_append]
    congr 2
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    congr 3
    omega
  · rw [nxt_one, key, b1]; omega
  · rw [nxt_one, key, b2, show 1 + n = n + 1 by omega]
    congr 1
    have := t_le_d (t := lev.t) hp1
    rw [← hd, hn] at this
    exact Nat.min_eq_left this
  · rw [nxt_one, key, posRest_caps]; rfl

/-- **An opening** whose commitment's cap was read: one value `.rows i ps r` at the current positions. -/
theorem item_open {i : ℕ} (s : AS) (hc : i < s.1.caps.length) :
    ∃ r, segV π L tr [.open i] s = [.rows i s.1.ps r] ∧ (nxt π L tr [.open i] s).1.caps = s.1.caps := by
  rw [segV_one, nxt_one]
  show ∃ r, ((((PA π L tr).opn i (clr s)).1.acc.map (V.NV.val π)).reverse = _) ∧ ((PA π L tr).opn i s).1.caps = _
  have hx : s.1.caps[i]? = some s.1.caps[i] := List.getElem?_eq_getElem hc
  obtain ⟨o, ht, w⟩ := s.1.caps[i]
  simp only [PA, clr, hx]
  exact ⟨_, rfl, rfl⟩

end Caps

/-! ## Draw values as `E2` numbers -/

theorem e2Nat_chal (a : Digest) : Whir.e2Nat (e2OfE (Lvm.FS.chalOf a)) = Lvm6.Q.drawN a := by
  have h1 := answerBits_mod a
  rw [Lvm.VEq.answerBits_eq] at h1
  rw [← h1]
  simp only [Whir.e2Nat, e2OfE, LeanVM.Protocol.Verifier.eToNat]
  have b0 := ((Lvm.FS.chalOf a).limb 0).toBitVec.isLt
  have b1 := ((Lvm.FS.chalOf a).limb 1).toBitVec.isLt
  simp only [LeanVM.Protocol.Verifier.kToNat] at *
  omega

/-! ## V1's positions are W1's -/

theorem posE2_posAll (tr : Trace) {h c d T : ℕ} (hc : 0 < c) (hT : T ≤ d * c) (hcp : 128 / h = c) (i0 n : ℕ)
    (hn : d ≤ n) :
    List.ofFn (fun k : Fin T ↦ (Whir.posE2 h c d T hc hT (fun k' ↦ ((((List.range n).map fun m ↦
      Lvm.FS.chalOf (aOf tr (i0 + m)))).map e2OfE).getD k' 0) k : ℕ)) = posAll tr i0 h T := by
  apply List.ext_getElem (by simp [posAll])
  intro k h1 h2
  simp only [List.length_ofFn] at h1
  have hk : k / c < n := by
    have : k / c < d := (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
    omega
  simp only [List.getElem_ofFn, posAll, List.getElem_map, List.getElem_range, Whir.posE2, Lvm6.Q.posOf,
    Nat.shiftRight_eq_div_pow]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  rw [e2Nat_chal, hcp, ← pow_mul, Nat.mul_comm h]

theorem rowsF_single {F : List Ev → ℕ × List ℕ} {E : List Ev} {i : ℕ} {ps : List ℕ} {r : List (List K)}
    (h : (i, ps) = F E) : RowsF F E [.rows i ps r] := by
  intro pre i' ps' r' post he
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, V.Val.rows.injEq] at he
    obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := he
    simpa using h
  | cons x pre' => simp at he

theorem rep_ps_keep (π : ByteArray) (L : List V.Lev) (tr : Trace) :
    ∀ m (t : AS), (V.Prims.rep (PA π L tr) ((PA π L tr).draw V.tt V.keepPs) m t).1.ps = t.1.ps
  | 0, _ => rfl
  | m + 1, t => (rep_ps_keep π L tr m _).trans rfl

/-! ## The opening blocks at `P18` -/

section Blocks

variable (ws : List Word)

/-- What the draws between a position group and its opening do: draws, positions and caps kept. -/
def ExOK (ex : List V.Item) (ne : ℕ) : Prop :=
  ∀ t : AS, segV πW P18.levs τW ex t = (List.range ne).map (fun x ↦ V.NV.val πW (.draw (aOf τW (t.2 + x)))) ∧
    (nxt πW P18.levs τW ex t).1.ps = t.1.ps ∧ (nxt πW P18.levs τW ex t).1.caps = t.1.caps

theorem exOK_nil : ExOK ws [] 0 := fun _ ↦ ⟨rfl, rfl, rfl⟩

theorem exOK_D1 : ExOK ws [.D 1] 1 := fun t ↦
  ⟨(item_D πW P18.levs τW 1 t).1, rep_ps_keep πW P18.levs τW 1 t,
    rep_caps πW P18.levs τW (f := (PA πW P18.levs τW).draw V.tt V.keepPs) (fun _ ↦ rfl) 1 t⟩

/-- **A position group, the draws after it, the opening**: the opening value is `F18` of the values before. -/
theorem rowsF_block {j g : ℕ} {ex : List V.Item} {ne : ℕ} (hex : ExOK ws ex ne) {h c T d : ℕ} (hc : 0 < c)
    (hT : T ≤ d * c) (hT1 : 1 ≤ T)
    (hlev : (P18.levs.getD j default).ht = h ∧ (P18.levs.getD j default).t = T ∧
      V.Lev.per (P18.levs.getD j default) = c ∧ V.Lev.draws (P18.levs.getD j default) = d)
    (hpos : ∀ E, posAt j E = List.ofFn fun k : Fin T ↦
      (Whir.posE2 h c d T hc hT (fun k' ↦ (lastS E (d + ne)).getD k' 0) k : ℕ))
    (s : AS) (E : List Ev) (hq : qcount E = j) (hcap : j < s.1.caps.length) :
    RowsF F18 E (segV πW P18.levs τW ([.pos j g] ++ ex ++ [.open j]) s) ∧
      qcount ((segV πW P18.levs τW ([.pos j g] ++ ex ++ [.open j]) s).map toEv) = 1 ∧
      (nxt πW P18.levs τW ([.pos j g] ++ ex ++ [.open j]) s).1.caps = s.1.caps := by
  obtain ⟨hht, hTT, hper, hdd⟩ := hlev
  obtain ⟨v1, n1, p1, c1⟩ := item_pos πW P18.levs τW (i := j) (g := g) (by omega) (by omega) s
  obtain ⟨v2, p2, c2⟩ := hex (nxt πW P18.levs τW [.pos j g] s)
  obtain ⟨r, v3, c3⟩ := item_open πW P18.levs τW (i := j)
    (nxt πW P18.levs τW ex (nxt πW P18.levs τW [.pos j g] s)) (by rw [c2, c1]; exact hcap)
  rw [hdd] at v1 n1
  rw [hht, hTT] at p1
  have hseg : segV πW P18.levs τW ([.pos j g] ++ ex ++ [.open j]) s =
      (V.Val.e (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8)) ::
        ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m))).map V.Val.c) ++
      [.rows j (posAll τW s.2 h T) r] := by
    rw [segV_append, segV_append, nxt_append, v1, v2, v3, p2, p1, n1]
    simp only [List.range_add, List.map_append, List.map_map, List.cons_append, List.append_assoc,
      Function.comp_def, V.NV.val, Nat.add_assoc]
  have hnr : NoRows (V.Val.e (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8)) ::
      ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m))).map V.Val.c) := by
    intro v hv i ps r'
    simp only [List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨_, _, rfl⟩ <;> simp
  have hev : (V.Val.e (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8)) ::
      ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m))).map V.Val.c).map toEv =
      Ev.read (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8)) ::
        ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m))).map Ev.sample := by
    simp only [List.map_cons, List.map_map, Function.comp_def, toEv]
  rw [hseg]
  refine ⟨rowsF_append (rowsF_noRows hnr) (rowsF_single ?_), ?_, ?_⟩
  · have hl := lastS_grp E (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8))
      ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m)))
    rw [List.length_map, List.length_range] at hl
    have hq' : qcount (E ++ Ev.read (Lvm.FS.eOfBytes (((Lvm.Replay.bl πW).drop s.1.off).take 8)) ::
        ((List.range (d + ne)).map fun m ↦ Lvm.FS.chalOf (aOf τW (s.2 + m))).map Ev.sample) = j := by
      rw [qcount_append, qcount_grp, hq, Nat.add_zero]
    rw [hev, F18, hq', hpos, hl]
    have hcp : 128 / h = c := by rw [← hht, ← hper]; rfl
    rw [posE2_posAll τW hc hT hcp s.2 (d + ne) (by omega)]
  · rw [List.map_append, qcount_append, qcount_noRows hnr]; simp [qcount, toEv, isQ]
  · rw [nxt_append, nxt_append, c3, c2, c1]

end Blocks

/-! ## The levels of `P18` -/

theorem allPc_rep (n : ℕ) (l : List V.Item) (h : ∀ x ∈ l, pcB x = true) : ∀ x ∈ rep n l, pcB x = true := by
  intro x hx
  simp only [rep, List.mem_flatten, List.mem_replicate] at hx
  obtain ⟨_, ⟨-, rfl⟩, hx⟩ := hx
  exact h x hx

theorem capsSum_rep (n : ℕ) (l : List V.Item) (h : (l.map capsN).sum = 0) : ((rep n l).map capsN).sum = 0 := by
  simp [rep, List.map_flatten, List.sum_flatten, h]

theorem capsSum_plain {l : List V.Item} (h : ∀ it ∈ l, plainB it = true) : (l.map capsN).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
  have := h it hit
  cases it <;> simp_all [plainB, capsN]

/-- A mid level's items before its position group. -/
def Amid (j : ℕ) : List V.Item :=
  rep (P18.lvl j).fold [.E 4, .G (P18.lvl j).gFold, .D 1] ++ [.E (P18.lvl j).fold, .cap (j + 1), .B,
    .G (P18.lvl (j + 1)).gOod, .D (P18.nu (j + 1) - 1), .E 1]

/-- The final level's items before its position group, and its tail rounds. -/
def Afin : List V.Item := rep (P18.lvl 4).fold [.E 4, .G (P18.lvl 4).gFold, .D 1] ++ [.E P18.finalLen]
def Tfin : List V.Item := rep P18.tail (rnd 2 P18.gr.tail)

theorem lp_mid {j : ℕ} (hj : j < 4) : P18.levelPart j =
    Amid j ++ ([.pos j (P18.lvl j).gQuery] ++ [.D 1] ++ [.open j]) := by
  rw [Shape.levelPart, if_pos (show j + 1 < P18.levels.length from show j + 1 < 5 by omega)]
  simp [Amid]

theorem lp_fin : P18.levelPart 4 = Afin ++ (([.pos 4 (P18.lvl 4).gQuery] ++ [] ++ [.open 4]) ++ Tfin) := by
  rw [Shape.levelPart, if_neg (show ¬ (4 + 1 < P18.levels.length) from show ¬ (4 + 1 < 5) by omega)]
  simp [Afin, Tfin]

theorem openPart_eq : P18.openPart =
    P18.levelPart 0 ++ (P18.levelPart 1 ++ (P18.levelPart 2 ++ (P18.levelPart 3 ++ P18.levelPart 4))) := by
  rw [Shape.openPart, show P18.levels.length = 5 from rfl]
  simp [List.range_succ]

theorem lev0 : (P18.levs.getD 0 default).ht = 21 ∧ (P18.levs.getD 0 default).t = 110 ∧
    V.Lev.per (P18.levs.getD 0 default) = 6 ∧ V.Lev.draws (P18.levs.getD 0 default) = 19 := by decide
theorem lev1 : (P18.levs.getD 1 default).ht = 20 ∧ (P18.levs.getD 1 default).t = 45 ∧
    V.Lev.per (P18.levs.getD 1 default) = 6 ∧ V.Lev.draws (P18.levs.getD 1 default) = 8 := by decide
theorem lev2 : (P18.levs.getD 2 default).ht = 19 ∧ (P18.levs.getD 2 default).t = 28 ∧
    V.Lev.per (P18.levs.getD 2 default) = 6 ∧ V.Lev.draws (P18.levs.getD 2 default) = 5 := by decide
theorem lev3 : (P18.levs.getD 3 default).ht = 18 ∧ (P18.levs.getD 3 default).t = 21 ∧
    V.Lev.per (P18.levs.getD 3 default) = 7 ∧ V.Lev.draws (P18.levs.getD 3 default) = 3 := by decide
theorem lev4 : (P18.levs.getD 4 default).ht = 17 ∧ (P18.levs.getD 4 default).t = 18 ∧
    V.Lev.per (P18.levs.getD 4 default) = 7 ∧ V.Lev.draws (P18.levs.getD 4 default) = 3 := by decide

/-- W1's level positions (`posAt`), unfolded (`qPos`/`fPos` of `midE`/`finE`'s `posE2`). -/
theorem posAt0 (E : List Ev) : posAt 0 E = List.ofFn fun k : Fin 110 ↦
    (Whir.posE2 21 6 19 110 (by norm_num) (by norm_num) (fun k' ↦ (lastS E (19 + 1)).getD k' 0) k : ℕ) := rfl
theorem posAt1 (E : List Ev) : posAt 1 E = List.ofFn fun k : Fin 45 ↦
    (Whir.posE2 20 6 8 45 (by norm_num) (by norm_num) (fun k' ↦ (lastS E (8 + 1)).getD k' 0) k : ℕ) := rfl
theorem posAt2 (E : List Ev) : posAt 2 E = List.ofFn fun k : Fin 28 ↦
    (Whir.posE2 19 6 5 28 (by norm_num) (by norm_num) (fun k' ↦ (lastS E (5 + 1)).getD k' 0) k : ℕ) := rfl
theorem posAt3 (E : List Ev) : posAt 3 E = List.ofFn fun k : Fin 21 ↦
    (Whir.posE2 18 7 3 21 (by norm_num) (by norm_num) (fun k' ↦ (lastS E (3 + 1)).getD k' 0) k : ℕ) := rfl
theorem posAt4 (E : List Ev) : posAt 4 E = List.ofFn fun k : Fin 18 ↦
    (Whir.posE2 17 7 3 18 (by norm_num) (by norm_num) (fun k' ↦ (lastS E (3 + 0)).getD k' 0) k : ℕ) := rfl

section Levels

variable (ws : List Word)

theorem rowsF_mid {j : ℕ} (hj : j < 4) {h c T d : ℕ} (hc : 0 < c) (hT : T ≤ d * c) (hT1 : 1 ≤ T)
    (hlev : (P18.levs.getD j default).ht = h ∧ (P18.levs.getD j default).t = T ∧
      V.Lev.per (P18.levs.getD j default) = c ∧ V.Lev.draws (P18.levs.getD j default) = d)
    (hpos : ∀ E, posAt j E = List.ofFn fun k : Fin T ↦
      (Whir.posE2 h c d T hc hT (fun k' ↦ (lastS E (d + 1)).getD k' 0) k : ℕ))
    (s : AS) (E : List Ev) (hq : qcount E = j) (hcap : s.1.caps.length = j + 1) :
    RowsF F18 E (segV πW P18.levs τW (P18.levelPart j) s) ∧
      qcount ((segV πW P18.levs τW (P18.levelPart j) s).map toEv) = 1 ∧
      (nxt πW P18.levs τW (P18.levelPart j) s).1.caps.length = j + 2 := by
  rw [lp_mid hj, segV_append, nxt_append]
  have hpc : ∀ it ∈ Amid j, pcB it = true := by
    intro it hit
    rcases List.mem_append.mp hit with hit | hit
    · exact allPc_rep _ _ (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl) it hit
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn := noRows_pc πW P18.levs τW _ hpc s
  have hcA := walk_caps πW P18.levs τW (Amid j) s
  have hsum : ((Amid j).map capsN).sum = 1 := by
    rw [Amid, List.map_append, List.sum_append, capsSum_rep _ _ (by simp [capsN])]
    simp [capsN]
  have hq' : qcount (E ++ (segV πW P18.levs τW (Amid j) s).map toEv) = j := by
    rw [qcount_append, qcount_noRows hn, hq, Nat.add_zero]
  obtain ⟨b1, b2, b3⟩ := rowsF_block ws (g := (P18.lvl j).gQuery) (exOK_D1 ws) hc hT hT1 hlev hpos
    (nxt πW P18.levs τW (Amid j) s) _ hq' (by rw [hcA, hcap, hsum]; omega)
  refine ⟨rowsF_append (rowsF_noRows hn) b1, ?_, ?_⟩
  · rw [List.map_append, qcount_append, qcount_noRows hn, b2]
  · rw [b3, hcA, hcap, hsum]

theorem rowsF_fin (s : AS) (E : List Ev) (hq : qcount E = 4) (hcap : s.1.caps.length = 5) :
    RowsF F18 E (segV πW P18.levs τW (P18.levelPart 4) s) := by
  rw [lp_fin, segV_append, segV_append]
  have hpc : ∀ it ∈ Afin, pcB it = true := by
    intro it hit
    rcases List.mem_append.mp hit with hit | hit
    · exact allPc_rep _ _ (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl) it hit
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      subst hit; rfl
  have hpt : ∀ it ∈ Tfin, pcB it = true :=
    allPc_rep _ _ (by
      intro x hx; simp only [rnd, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl)
  have hn := noRows_pc πW P18.levs τW _ hpc s
  have hcA := walk_caps πW P18.levs τW Afin s
  have hsum : (Afin.map capsN).sum = 0 := by
    rw [Afin, List.map_append, List.sum_append, capsSum_rep _ _ (by simp [capsN])]
    simp [capsN]
  have hq' : qcount (E ++ (segV πW P18.levs τW Afin s).map toEv) = 4 := by
    rw [qcount_append, qcount_noRows hn, hq, Nat.add_zero]
  obtain ⟨b1, -, -⟩ := rowsF_block ws (g := (P18.lvl 4).gQuery) (exOK_nil ws) (by norm_num) (by norm_num)
    (by norm_num) lev4 posAt4 (nxt πW P18.levs τW Afin s) _ hq' (by rw [hcA, hcap, hsum]; omega)
  exact rowsF_append (rowsF_noRows hn) (rowsF_append b1 (rowsF_noRows (noRows_pc πW P18.levs τW _ hpt _)))

/-- **Item 1 of N4-tail, V1's side**: V1's opening values carry `F18` of the values before them. -/
theorem rowsF_segO : RowsF F18 [] (segO ws) := by
  have hc0 : (stAt ws preO).1.caps.length = 1 := by
    rw [stAt, walk_caps]
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
    rw [e, List.map_append, List.sum_append, capsSum_plain hp, commitPart_eq]
    rfl
  unfold segO segAt
  rw [openPart_eq]
  rw [segV_append πW P18.levs τW (P18.levelPart 0), segV_append πW P18.levs τW (P18.levelPart 1),
    segV_append πW P18.levs τW (P18.levelPart 2), segV_append πW P18.levs τW (P18.levelPart 3)]
  obtain ⟨r0, q0, c0⟩ := rowsF_mid ws (j := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lev0
    posAt0 (stAt ws preO) [] rfl hc0
  have e1 : qcount ([] ++ (segV πW P18.levs τW (P18.levelPart 0) (stAt ws preO)).map toEv) = 1 := by
    rw [List.nil_append, q0]
  obtain ⟨r1, q1, c1⟩ := rowsF_mid ws (j := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lev1
    posAt1 _ _ e1 c0
  have e2 := qcount_append ([] ++ (segV πW P18.levs τW (P18.levelPart 0) (stAt ws preO)).map toEv)
    ((segV πW P18.levs τW (P18.levelPart 1) (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO))).map toEv)
  rw [e1, q1] at e2
  obtain ⟨r2, q2, c2⟩ := rowsF_mid ws (j := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lev2
    posAt2 _ _ e2 c1
  have e3 := qcount_append (([] ++ (segV πW P18.levs τW (P18.levelPart 0) (stAt ws preO)).map toEv) ++
    (segV πW P18.levs τW (P18.levelPart 1) (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO))).map toEv)
    ((segV πW P18.levs τW (P18.levelPart 2) (nxt πW P18.levs τW (P18.levelPart 1)
      (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO)))).map toEv)
  rw [e2, q2] at e3
  obtain ⟨r3, q3, c3⟩ := rowsF_mid ws (j := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lev3
    posAt3 _ _ e3 c2
  have e4 := qcount_append ((([] ++ (segV πW P18.levs τW (P18.levelPart 0) (stAt ws preO)).map toEv) ++
    (segV πW P18.levs τW (P18.levelPart 1) (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO))).map toEv) ++
    (segV πW P18.levs τW (P18.levelPart 2) (nxt πW P18.levs τW (P18.levelPart 1)
      (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO)))).map toEv)
    ((segV πW P18.levs τW (P18.levelPart 3) (nxt πW P18.levs τW (P18.levelPart 2) (nxt πW P18.levs τW
      (P18.levelPart 1) (nxt πW P18.levs τW (P18.levelPart 0) (stAt ws preO))))).map toEv)
  rw [e3, q3] at e4
  have r4 := rowsF_fin ws _ _ e4 c3
  exact rowsF_append r0 (rowsF_append r1 (rowsF_append r2 (rowsF_append r3 r4)))

end Levels

end Lvm6.Node.Split
