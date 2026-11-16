-- New for lvm2 E2F (E2F-QH4): the specs of the `E2` Keccak layer's template gadgets (`LvmE2QKTB`, `LvmE2QKLayer`)
-- against the generic weight forms (`LvmQEqKeccakAlgG`) at `FE2`, and the tools to walk an `E2` template
-- (`THold2`), the `E2` counterparts of `LvmQKeccakParts`/`Parts2`/`Rounds` and `LvmQEqKeccakLayer2`.
import LvmE2QKRead
import LvmQEqKeccakAlgG
import LvmQEqKeccakGkr

/-!
# `E2` layer gadgets: specs and template walking

* `gx = x ∈ FE2`; **gadget specs** in `FE2`: `q2Proj_spec` (`V`'s projected sum), `q2Powers_spec`, `q2Inst_spec`
  (`powersF`), `q2LowTab_spec`/`q2HighTab_spec`/`q2Shift_spec` (`lowTabG`, `highTabG`, `shiftLHG`),
  `q2LaneForm_spec`, `q2Flip_spec`, `q2LaneW_spec`, `q2Index_spec` (`indexProdG gx`);
* the stream: `lv2 xv str q` (lanes `q`, `q + 1` as an `E2` value); **`packSpec2`** (`V`'s `packRoundsD` on a
  view, its proof-of-work flags) with `q2PackRounds_spec`; `q2LocalRounds_spec` (`scSpec2`, four coefficients);
* `NoA` of every `E2` gadget; **`TInv2`** (`TInv` on `THold2`) with `peelN2`, `peelL2`, `peelA2` (the
  coordinatewise assertion), `inv_end2`; the copy rows (`cp2_get`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.E2V DM

/-! ## Values -/

/-- `x` in `FE2`. -/
def gx : FE2 := FE2.ofK FK.x

theorem fe2_ofK_pow (a : FK) (n : Nat) : FE2.ofK (a ^ n) = FE2.ofK a ^ n := map_pow FE2.ofKRingHom a n

theorem getD_valF2 {xv : Src → FE} {V : Nat → FE} (l : List S2) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (vals2 xv V l).getD i 0 := by
  simp [List.getD_eq_getElem _ _ hi, hi]

/-- `mapT2_spec` with the elements' membership. -/
theorem mapT2_spec_mem {α β : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB β} {P : α → β → Prop} :
    ∀ (as : List α), (∀ a ∈ as, ∀ n, THold2 xv V n (f a n).2 → P a (f a n).1) →
      ∀ (n : Nat), THold2 xv V n (mapT2 f as n).2 → List.Forall₂ P as (mapT2 f as n).1
  | [], _, _, _ => List.Forall₂.nil
  | a :: as, hf, n, h => by
    simp only [mapT2, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold2_append] at h
    exact List.Forall₂.cons (hf a (by simp) n h.1) (mapT2_spec_mem as (fun b hb => hf b (by simp [hb])) _ h.2)

/-! ## The RMFE projection and the instance weights -/

theorem projSrcs2_map {xv : Src → FE} {V : Nat → FE} (masks : List Nat) (c : Nat) (mu : List S2) :
    vals2 xv V (projSrcs2 masks mu c) =
      ((vals2 xv V mu).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none := by
  rw [projSrcs2, vals2, List.map_filterMap, List.zip_map_left, List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  split <;> rfl

theorem q2Proj_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (masks : List Nat)
    (mu prod : List S2) (n : Nat) (h : THold2 xv V n (q2Proj z masks mu prod n).2) :
    (q2Proj z masks mu prod n).1.valF xv V = sumF ((List.range prod.length).map fun c =>
      sumF (((vals2 xv V mu).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        (prod.getD c default).valF xv V) := by
  rw [sumF_eq_sum]
  refine q2SumMap_spec hz (fun c _ m hm => ?_) n h
  obtain ⟨h1, h2⟩ := (thold2_bind _ _).mp hm
  rw [tb_bind, q2Mul_spec h2, q2Sum_spec _ _ _ h1, hz, zero_add, add_zero, projSrcs2_map, sumF_eq_sum]

theorem q2Powers_spec {xv : Src → FE} {V : Nat → FE} {z s : S2} (hz : z.valF xv V = 0) :
    ∀ (k : Nat) (acc : S2) (n : Nat), THold2 xv V n (q2Powers z s acc k n).2 →
      vals2 xv V (q2Powers z s acc k n).1 = powersFromF (acc.valF xv V) (s.valF xv V) k
  | 0, _, _, _ => rfl
  | k + 1, acc, n, h => by
    simp only [q2Powers] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    simp only [tb_bind, tb_pure, vals2, List.map_cons, powersFromF]
    rw [← vals2, q2Powers_spec hz k _ _ h2, q2Mul_spec h1, hz, add_zero]

theorem q2Powers_length (z s : S2) : ∀ (k : Nat) (acc : S2) (n : Nat), (q2Powers z s acc k n).1.length = k
  | 0, _, _ => rfl
  | k + 1, acc, n => by simp [q2Powers, tb_bind, tb_pure, q2Powers_length z s k]

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` (`instWeightsF`'s terms) and `κ = Σ μ`. -/
theorem q2Inst_spec {xv : Src → FE} {V : Nat → FE} {z one s : S2} (hz : z.valF xv V = 0)
    (hone : one.valF xv V = 1) (embs : List Nat) (n : Nat) (h : THold2 xv V n (q2Inst z one s embs n).2) :
    vals2 xv V (q2Inst z one s embs n).1.1 =
        embs.map (fun e => sumF ((List.range embedBits).filterMap fun b =>
          if e.testBit b then some ((powersF (s.valF xv V) embedBits).getD b 0) else none)) ∧
    (q2Inst z one s embs n).1.2.valF xv V = (vals2 xv V (q2Inst z one s embs n).1.1).sum := by
  obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h3, -⟩ := (thold2_bind _ _).mp h
  have epw := q2Powers_spec hz embedBits one n h1
  rw [hone] at epw
  have hlen := q2Powers_length z s embedBits one n
  have k2 := mapT2_spec (P := fun e x => S2.valF xv V x = sumF ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some ((powersF (s.valF xv V) embedBits).getD b 0) else none))
    (fun e m hm => by
      rw [q2Sum_spec _ _ _ hm, hz, zero_add, sumF_eq_sum]
      congr 1
      simp only [embSrcs2, vals2, List.map_filterMap]
      apply List.filterMap_congr
      intro b hb
      split
      · simp only [Option.map_some, Option.some.injEq]
        rw [getD_valF2 _ (by rw [hlen]; simpa using hb), epw]; rfl
      · rfl) embs _ h2
  refine ⟨?_, ?_⟩
  · simp only [q2Inst, tb_bind, tb_pure]
    exact forall₂_map_eq2 k2
  · simp only [q2Inst, tb_bind, tb_pure]
    rw [q2Sum_spec _ _ _ h3, hz, zero_add]

/-! ## The shift tables, lane forms, flips, lane weights, `indexMle` -/

theorem q2LowTab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {ta tb : List S2}
    {a b : List FE2} (hta : vals2 xv V ta = eqKernelF (a.take 3)) (htb : vals2 xv V tb = eqKernelF (b.take 3))
    (ha : 3 ≤ a.length) (hb : 3 ≤ b.length) (c rl : Nat) (n : Nat) (h : THold2 xv V n (q2LowTab z ta tb c rl n).2) :
    (q2LowTab z ta tb c rl n).1.valF xv V = lowTabG a b c rl := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernelF_length] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernelF_length] at this; simp [this, hb]
  rw [lowTabG, sumF_eq_sum]
  refine q2SumMap_spec hz (fun zz hzz m hm => ?_) n h
  by_cases hc : (zz + rl) / 8 = c
  · simp only [hc, if_true] at hm ⊢
    rw [q2Mul_spec hm, hz, add_zero, getD_valF2 _ (by omega), getD_valF2 _ (by rw [la]; exact Nat.mod_lt _ (by omega)),
      hta, htb]
    rfl
  · simp only [hc, if_false] at hm ⊢
    exact hz

theorem q2HighTab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {ta tb : List S2}
    {a b : List FE2} (hta : vals2 xv V ta = eqKernelF (a.drop 3)) (htb : vals2 xv V tb = eqKernelF (b.drop 3))
    (ha : a.length = 6) (hb : b.length = 6) (k : Nat) (n : Nat) (h : THold2 xv V n (q2HighTab z ta tb k n).2) :
    (q2HighTab z ta tb k n).1.valF xv V = highTabG a b k := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernelF_length] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernelF_length] at this; simp [this, hb]
  rw [highTabG, sumF_eq_sum]
  refine q2SumMap_spec hz (fun zz hzz m hm => ?_) n h
  rw [q2Mul_spec hm, hz, add_zero, getD_valF2 _ (by omega), getD_valF2 _ (by rw [la]; exact Nat.mod_lt _ (by omega)),
    hta, htb]
  rfl

theorem q2Shift_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {L0 L1 H : List S2}
    {a b : List FE2} (h0 : vals2 xv V L0 = (List.range 8).map (lowTabG a b 0))
    (h1 : vals2 xv V L1 = (List.range 8).map (lowTabG a b 1)) (hH : vals2 xv V H = (List.range 8).map (highTabG a b))
    {r : Nat} (hr : r < 64) (n : Nat) (h : THold2 xv V n (q2Shift z L0 L1 H r n).2) :
    (q2Shift z L0 L1 H r n).1.valF xv V = shiftLHG a b r := by
  have l0 : L0.length = 8 := by simpa using congrArg List.length h0
  have l1 : L1.length = 8 := by simpa using congrArg List.length h1
  have lH : H.length = 8 := by simpa using congrArg List.length hH
  obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp h
  rw [q2Shift, tb_bind, q2Mul_spec g2, q2Mul_spec g1, hz, add_zero,
    getD_valF2 _ (by rw [l0]; exact Nat.mod_lt _ (by omega)), getD_valF2 _ (by rw [lH]; omega),
    getD_valF2 _ (by rw [l1]; exact Nat.mod_lt _ (by omega)), getD_valF2 _ (by rw [lH]; exact Nat.mod_lt _ (by omega)),
    h0, h1, hH]
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ (show 0 < 8 by omega), show r / 8 < 8 by omega,
    Nat.mod_lt _ (show 0 < 8 by omega), shiftLHG]

theorem q2LaneForm_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {B : List S2}
    (hB : 25 ≤ B.length) (R : Nat → S2) {l : Nat} (hl : l < 25) (n : Nat)
    (h : THold2 xv V n (q2LaneForm z B R l n).2) :
    (q2LaneForm z B R l n).1.valF xv V = laneFormF (vals2 xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h'⟩ := (thold2_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold2_bind _ _).mp h'
  have hp : ∀ x y, x < 5 → y < 5 → keccakPi (x + 5 * y) < B.length := fun x y hx hy =>
    lt_of_lt_of_le (kPi_lt _ (by omega)) hB
  rw [q2LaneForm, tb_bind, tb_bind, q2Dot_spec _ _ _ g3, q2Dot_spec _ _ _ g2, q2Mul_spec g1, hz, add_zero,
    laneFormF, sumF_eq_sum, sumF_eq_sum, getD_valF2 _ (lt_of_lt_of_le (kPi_lt _ hl) hB)]
  simp only [List.map_map, Function.comp_def]
  congr 2
  · congr 1
    apply List.map_congr_left
    intro y hy
    rw [getD_valF2 _ (hp _ _ (Nat.mod_lt _ (by omega)) (List.mem_range.mp hy))]
  · apply List.map_congr_left
    intro y hy
    rw [getD_valF2 _ (hp _ _ (Nat.mod_lt _ (by omega)) (List.mem_range.mp hy))]

theorem q2Flip_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {B A : List S2}
    (hB : 25 ≤ B.length) (hA : A.length = 64) (i n : Nat) (h : THold2 xv V n (q2Flip z B A i n).2) :
    (q2Flip z B A i n).1.valF xv V = flipFormG (vals2 xv V B) (fun s => (vals2 xv V A).getD s 0) i := by
  rw [q2Flip, q2LaneForm_spec hz hB _ (by omega) n h, flipFormG]
  congr 1
  funext s
  rw [getD_valF2 _ (by rw [hA]; exact Nat.mod_lt _ (by omega))]

theorem q2LaneW_spec {xv : Src → FE} {V : Nat → FE} {eL : List S2} (hL : 25 ≤ eL.length) (beta : S2) (n : Nat)
    (h : THold2 xv V n (q2LaneW eL beta n).2) :
    vals2 xv V (q2LaneW eL beta n).1 = (List.range 25).map fun l => (vals2 xv V eL).getD l 0 + beta.valF xv V *
      ((vals2 xv V eL).getD (keccakAlong (64 * l) 4 / 64) 0 + beta.valF xv V *
        (vals2 xv V eL).getD (keccakAlong (64 * l) 3 / 64) 0) := by
  refine forall₂_map_eq2 (mapT2_spec_mem (P := fun l x => S2.valF xv V x = _) _ (fun l hl m hm => ?_) n h)
  have hl' := List.mem_range.mp hl
  obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp hm
  rw [tb_bind, q2Mul_spec g2, q2Mul_spec g1, getD_valF2 (i := l) eL (by omega),
    getD_valF2 (i := keccakAlong (64 * l) 3 / 64) eL (lt_of_lt_of_le (along_lt l hl').1 hL),
    getD_valF2 (i := keccakAlong (64 * l) 4 / 64) eL (lt_of_lt_of_le (along_lt l hl').2 hL)]
  ring

theorem q2IndexStep_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (k : Nat) (acc r : S2)
    (n : Nat) (h : THold2 xv V n (q2IndexStep z k acc r n).2) :
    (q2IndexStep z k acc r n).1.valF xv V = acc.valF xv V * (1 + r.valF xv V * (1 + gx ^ (2 ^ k))) := by
  obtain ⟨g1, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold2_bind _ _).mp h
  rw [q2IndexStep, tb_bind, tb_bind, q2Mul_spec g3, q2One_spec g2, q2Scale_spec g1, hz, add_zero, fe2_ofK_add,
    fe2_ofK_one, fe2_ofK_pow, gx]
  ring

/-- `indexProdG` of `rs` from coordinate `k`: `Π_t (1 + r_t·(1 + g^(2^(k + t))))`. -/
theorem q2Index_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) :
    ∀ (rs : List S2) (k : Nat) (acc : S2) (n : Nat), THold2 xv V n (q2Index z k acc rs n).2 →
      (q2Index z k acc rs n).1.valF xv V =
        acc.valF xv V * ∏ t ∈ Finset.range rs.length, (1 + (vals2 xv V rs).getD t 0 * (1 + gx ^ (2 ^ (k + t))))
  | [], k, acc, n, _ => by simp [q2Index, tb_pure]
  | r :: rs, k, acc, n, h => by
    obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp h
    have e1 := q2IndexStep_spec hz k acc r n g1
    have e2 := q2Index_spec hz rs (k + 1) _ _ g2
    rw [e1] at e2
    show (q2Index z (k + 1) (q2IndexStep z k acc r n).1 rs (n + (q2IndexStep z k acc r n).2.length)).1.valF xv V = _
    rw [e2, List.length_cons, Finset.prod_range_succ']
    simp only [vals2, List.map_cons, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    conv_rhs => rw [Finset.prod_congr rfl (fun t _ => by rw [show k + (t + 1) = k + 1 + t by omega])]
    ring

/-! ## The stream -/

/-- Lanes `q`, `q + 1` of a loop's iteration fixed by `xv`, as an `E2` value. -/
def lv2 (xv : Src → FE) (str : List Nat) (q : Nat) : FE2 :=
  ⟨(xv (.ext ⟨.K, q, str⟩)).c₀, (xv (.ext ⟨.K, q + 1, str⟩)).c₀⟩

theorem lane2_valF (xv : Src → FE) (V : Nat → FE) (q : Nat) (str : List Nat) :
    (lane2 q str).valF xv V = lv2 xv str q := rfl

/-- **`V`'s `packRoundsD` on a view** (`v` the `E2` view, `va` the `E` answers' view): value, scale, challenges,
end position, proof-of-work flags. Round `14` lanes: `c₁, c₂`, the nonce, the answer. -/
def packSpec2 (v : Nat → FE2) (va : Nat → FE) (g : Nat) : List FE2 → FE2 → FE2 → Nat → FE2 × FE2 × List FE2 × Nat × Bool
  | [], value, scale, p => (value, scale, [], p, true)
  | r :: rs, value, scale, p =>
    let msg := (value + r * sumF (scalars2 v (p + 40) 2)) :: scalars2 v (p + 40) 2
    let ch := e2OfFE (va (p + 80))
    let res := packSpec2 v va g rs ((1 + r + ch) * polyEvalF msg ch) (scale * (1 + r + ch)) (p + 112)
    (res.1, res.2.1, ch :: res.2.2.1, res.2.2.2.1, powOKR g (va (p + 80)) && res.2.2.2.2)

theorem packSpec2_pos (v : Nat → FE2) (va : Nat → FE) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (p : Nat),
    (packSpec2 v va g pt value scale p).2.2.2.1 = p + 112 * pt.length
  | [], _, _, p => by simp [packSpec2]
  | r :: rs, value, scale, p => by
    simp only [packSpec2, List.length_cons]
    rw [packSpec2_pos v va g rs]
    ring

theorem packSpec2_length (v : Nat → FE2) (va : Nat → FE) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (p : Nat),
    (packSpec2 v va g pt value scale p).2.2.1.length = pt.length
  | [], _, _, _ => rfl
  | r :: rs, value, scale, p => by
    simp only [packSpec2, List.length_cons]
    rw [packSpec2_length v va g rs]

theorem q2PackRound_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {v : Nat → FE2}
    {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o)
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) (hN : q + 5 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (r value scale : S2) (n : Nat) (h : THold2 xv V n (q2PackRound z q str r value scale n).2) :
    (q2PackRound z q str r value scale n).1.1.valF xv V =
        (1 + r.valF xv V + e2OfFE (va (p + 80))) *
          polyEvalF ((value.valF xv V + r.valF xv V * sumF (scalars2 v (p + 40) 2)) :: scalars2 v (p + 40) 2)
            (e2OfFE (va (p + 80))) ∧
    (q2PackRound z q str r value scale n).1.2.1.valF xv V = scale.valF xv V * (1 + r.valF xv V + e2OfFE (va (p + 80))) ∧
    (q2PackRound z q str r value scale n).1.2.2.valF xv V = e2OfFE (va (p + 80)) := by
  unfold q2PackRound at h ⊢
  obtain ⟨h4, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h9, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h10, -⟩ := (thold2_bind _ _).mp h
  have e4 := q2Add_spec h4
  have e5 := q2Mul_spec h5
  have e6 := q2Mul_spec h6
  have e7 := q2Mul_spec h7
  have e8 := q2Lin_spec h8
  have e9 := q2Mul_spec h9
  have e10 := q2Mul_spec h10
  have c1 : (lane2 q str).valF xv V = v (p + 40) := by rw [lane2_valF, hv _ (by omega)]; congr 1; omega
  have c2 : (lane2 (q + 2) str).valF xv V = v (p + 56) := by rw [lane2_valF, hv _ (by omega)]; congr 1; omega
  have c3 : (lane2 (q + 5) str).valF xv V = e2OfFE (va (p + 80)) := by
    rw [lane2_valF, hv _ (by omega), hva]; congr 1; omega
  simp only [tb_bind, tb_pure]
  rw [c1, c2] at e4
  simp only [scalars2, List.range_succ, List.range_zero, List.map_append, List.map_nil, List.nil_append,
    List.map_cons, sumF, polyEvalF, List.cons_append, List.singleton_append, List.foldl_cons, List.foldl_nil,
    List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [e9, e8, e7, e6, e5, e4, c1, c2, c3, hz, fe2_ofK_one]
    ring
  · rw [e10, e8, c3, hz, fe2_ofK_one]
    ring
  · exact c3

/-- **The pack rounds are `V`'s `packSpec2`** (values, scale, challenges). -/
theorem q2PackRounds_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {v : Nat → FE2}
    {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o) (g : Nat)
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) :
    ∀ (rs : List S2) (q p : Nat), q + 14 * rs.length ≤ N → p + 40 = 8 * q + off → ∀ (value scale : S2) (n : Nat),
      THold2 xv V n (q2PackRounds z str q rs value scale n).2 →
      (q2PackRounds z str q rs value scale n).1.1.valF xv V =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).1 ∧
      (q2PackRounds z str q rs value scale n).1.2.1.valF xv V =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).2.1 ∧
      vals2 xv V (q2PackRounds z str q rs value scale n).1.2.2 =
          (packSpec2 v va g (vals2 xv V rs) (value.valF xv V) (scale.valF xv V) p).2.2.1
  | [], q, p, _, _, value, scale, n, _ => by simp [q2PackRounds, tb_pure, packSpec2]
  | r :: rs, q, p, hN, hp, value, scale, n, h => by
    simp only [q2PackRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    obtain ⟨e1, e2, e3⟩ := q2PackRound_spec hz hva hv (by simp at hN; omega) hp r value scale n h1
    have ih := q2PackRounds_spec hz hva g hv rs (q + 14) (p + 112) (by simp at hN; omega) (by omega) _ _ _ h2
    simp only [tb_bind, tb_pure, vals2, List.map_cons, packSpec2]
    rw [e1, e2] at ih
    exact ⟨ih.1, ih.2.1, congrArg₂ List.cons e3 ih.2.2⟩

theorem q2LocalRound_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE2} {va : Nat → FE}
    (hva : ∀ o, e2OfFE (va o) = v o)
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) (hN : q + 7 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (value : S2) (n : Nat) (h : THold2 xv V n (q2LocalRound q str value n).2) :
    (q2LocalRound q str value n).1.1.valF xv V =
        polyEvalF (roundPoly2 v p 4 (value.valF xv V)) (e2OfFE (va (ansAt2 p 4))) ∧
    (q2LocalRound q str value n).1.2.valF xv V = e2OfFE (va (ansAt2 p 4)) := by
  unfold q2LocalRound at h ⊢
  obtain ⟨h5, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold2_bind _ _).mp h
  obtain ⟨h9, -⟩ := (thold2_bind _ _).mp h
  have e5 := q2Add_spec h5
  have e6 := q2Add_spec h6
  have e7 := q2Mul_spec h7
  have e8 := q2Mul_spec h8
  have e9 := q2Mul_spec h9
  have c0 : (lane2 q str).valF xv V = v (p + 40) := by rw [lane2_valF, hv _ (by omega)]; congr 1; omega
  have c2 : (lane2 (q + 2) str).valF xv V = v (p + 56) := by rw [lane2_valF, hv _ (by omega)]; congr 1; omega
  have c3 : (lane2 (q + 4) str).valF xv V = v (p + 56 + 16) := by
    rw [lane2_valF, hv _ (by omega)]; congr 1; omega
  have ch : (lane2 (q + 7) str).valF xv V = e2OfFE (va (ansAt2 p 4)) := by
    rw [lane2_valF, hv _ (by omega), hva]; congr 1; simp only [ansAt2]; omega
  simp only [tb_bind, tb_pure]
  refine ⟨?_, ch⟩
  simp only [roundPoly2, scalars2, show (4 - 2 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumF, polyEvalF, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one]
  rw [e9, e8, e7, e6, e5, c0, c2, c3, ch]
  ring

/-- **The position rounds are `V`'s `scSpec2` with four coefficients.** -/
theorem q2LocalRounds_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE2} {va : Nat → FE}
    (hva : ∀ o, e2OfFE (va o) = v o) (g : Nat)
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv2 xv str m = v (8 * m + off)) :
    ∀ (k q p : Nat), q + 16 * k ≤ N → p + 40 = 8 * q + off → ∀ (value : S2) (n : Nat),
      THold2 xv V n (q2LocalRounds str k q value n).2 →
      (q2LocalRounds str k q value n).1.1.valF xv V = (scSpec2 v va g 4 p (value.valF xv V) k).2.1 ∧
      vals2 xv V (q2LocalRounds str k q value n).1.2 = (scSpec2 v va g 4 p (value.valF xv V) k).1
  | 0, q, p, _, _, value, n, _ => by simp [q2LocalRounds, tb_pure, scSpec2]
  | k + 1, q, p, hN, hp, value, n, h => by
    simp only [q2LocalRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold2_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold2_bind _ _).mp h
    obtain ⟨e1, e2⟩ := q2LocalRound_spec hva hv (by omega) hp value n h1
    have ih := q2LocalRounds_spec hva g hv k (q + 16) (p + roundLen2 4) (by omega) (by simp [roundLen2]; omega) _ _ h2
    simp only [tb_bind, tb_pure, vals2, List.map_cons, scSpec2]
    rw [e1] at ih
    exact ⟨ih.1, congrArg₂ List.cons e2 ih.2⟩

/-! ## No assertions -/

theorem noA_emit2 (f : E2Fn) (xs : List S2) : NoA (emit2 f xs) := by
  intro xv V n k hk ha
  simp only [emit2, e2I, List.length_cons, List.length_nil] at hk
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp [emit2, e2I] at ha

theorem noA_q2Mul (a b d : S2) : NoA (q2Mul a b d) := noA_emit2 _ _
theorem noA_q2Lin (k : FK) (k' : FE2) (a b : S2) : NoA (q2Lin k k' a b) := noA_emit2 _ _
theorem noA_q2Add (a b : S2) : NoA (q2Add a b) := noA_q2Lin _ _ _ _
theorem noA_q2One (a : S2) : NoA (q2One a) := noA_q2Lin _ _ _ _
theorem noA_q2Scale (k : FK) (a : S2) : NoA (q2Scale k a) := noA_q2Lin _ _ _ _
theorem noA_q2Copy (a : S2) : NoA (q2Copy a) := noA_q2Lin _ _ _ _
theorem noA_kLin (k k' : FK) (a b : Src) : NoA (kLin k k' a b) := noA_emit nofun

theorem noA_q2Base (b : Src) : NoA (q2Base b) :=
  noA_bind (noA_kLin _ _ _ _) fun _ => noA_bind (noA_kLin _ _ _ _) fun _ => noA_pure _

theorem noA_mapT2 {α β : Type} {f : α → TB β} (hf : ∀ a, NoA (f a)) : ∀ l : List α, NoA (mapT2 f l)
  | [] => noA_pure _
  | a :: as => noA_bind (hf a) fun _ => noA_bind (noA_mapT2 hf as) fun _ => noA_pure _

theorem noA_q2Sum : ∀ (s : S2) (cs : List S2), NoA (q2Sum s cs)
  | _, [] => noA_pure _
  | s, c :: cs => noA_bind (noA_q2Add s c) fun s' => noA_q2Sum s' cs

theorem noA_q2Dot : ∀ (acc : S2) (cds : List (S2 × S2)), NoA (q2Dot acc cds)
  | _, [] => noA_pure _
  | acc, _ :: rest => noA_bind (noA_q2Mul _ _ acc) fun a => noA_q2Dot a rest

theorem noA_q2Horner (x : S2) : ∀ (h : S2) (cs : List S2), NoA (q2Horner x h cs)
  | _, [] => noA_pure _
  | h, c :: cs => noA_bind (noA_q2Mul h x c) fun h' => noA_q2Horner x h' cs

theorem noA_q2EqStep (z : S2) (tab : List S2) (r : S2) : NoA (q2EqStep z tab r) :=
  noA_bind (noA_q2One r) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Mul _ _ _) _) fun _ =>
    noA_bind (noA_mapT2 (fun _ => noA_q2Mul _ _ _) _) fun _ => noA_pure _

theorem noA_q2EqTab (z : S2) : ∀ (tab pt : List S2), NoA (q2EqTab z tab pt)
  | _, [] => noA_pure _
  | tab, r :: rs => noA_bind (noA_q2EqStep z tab r) fun t => noA_q2EqTab z t rs

theorem noA_q2SumMap (z : S2) (k : Nat) {f : Nat → TB S2} (hf : ∀ c, NoA (f c)) : NoA (q2SumMap z k f) :=
  noA_bind (noA_mapT2 hf _) fun ts => noA_q2Sum z ts

theorem noA_q2Proj (z : S2) (masks : List Nat) (mu prod : List S2) : NoA (q2Proj z masks mu prod) :=
  noA_q2SumMap _ _ fun _ => noA_bind (noA_q2Sum _ _) fun _ => noA_q2Mul _ _ _

theorem noA_q2Powers (z s : S2) : ∀ (acc : S2) (k : Nat), NoA (q2Powers z s acc k)
  | _, 0 => noA_pure _
  | acc, k + 1 => noA_bind (noA_q2Mul acc s z) fun nx => noA_bind (noA_q2Powers z s nx k) fun _ => noA_pure _

theorem noA_q2Inst (z one s : S2) (embs : List Nat) : NoA (q2Inst z one s embs) :=
  noA_bind (noA_q2Powers _ _ _ _) fun _ => noA_bind (noA_mapT2 (fun _ => noA_q2Sum _ _) _) fun _ =>
    noA_bind (noA_q2Sum _ _) fun _ => noA_pure _

theorem noA_q2LowTab (z : S2) (ta tb : List S2) (c rl : Nat) : NoA (q2LowTab z ta tb c rl) :=
  noA_q2SumMap _ _ fun zz => by
    by_cases h : (zz + rl) / 8 = c
    · simp only [h, ite_true]; exact noA_q2Mul _ _ _
    · simp only [h, ite_false]; exact noA_pure _

theorem noA_q2HighTab (z : S2) (ta tb : List S2) (k : Nat) : NoA (q2HighTab z ta tb k) :=
  noA_q2SumMap _ _ fun _ => noA_q2Mul _ _ _

theorem noA_q2Shift (z : S2) (L0 L1 H : List S2) (r : Nat) : NoA (q2Shift z L0 L1 H r) :=
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2Mul _ _ _

theorem noA_q2LaneForm (z : S2) (B : List S2) (R : Nat → S2) (l : Nat) : NoA (q2LaneForm z B R l) :=
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Dot _ _) fun _ => noA_q2Dot _ _

theorem noA_q2Flip (z : S2) (B A : List S2) (i : Nat) : NoA (q2Flip z B A i) := noA_q2LaneForm _ _ _ _

theorem noA_q2LaneW (eL : List S2) (beta : S2) : NoA (q2LaneW eL beta) :=
  noA_mapT2 (fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2Mul _ _ _) _

theorem noA_q2IndexStep (z : S2) (k : Nat) (acc r : S2) : NoA (q2IndexStep z k acc r) :=
  noA_bind (noA_q2Scale _ _) fun _ => noA_bind (noA_q2One _) fun _ => noA_q2Mul _ _ _

theorem noA_q2Index (z : S2) : ∀ (k : Nat) (acc : S2) (rs : List S2), NoA (q2Index z k acc rs)
  | _, _, [] => noA_pure _
  | k, acc, r :: rs => noA_bind (noA_q2IndexStep z k acc r) fun acc' => noA_q2Index z (k + 1) acc' rs

theorem noA_q2PackRound (z : S2) (q : Nat) (str : List Nat) (r value scale : S2) :
    NoA (q2PackRound z q str r value scale) :=
  noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Lin _ _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_pure _

theorem noA_q2PackRounds (z : S2) (str : List Nat) :
    ∀ (q : Nat) (rs : List S2) (value scale : S2), NoA (q2PackRounds z str q rs value scale)
  | _, [], _, _ => noA_pure _
  | q, r :: rs, value, scale => noA_bind (noA_q2PackRound z q str r value scale) fun a =>
    noA_bind (noA_q2PackRounds z str (q + 14) rs a.1 a.2.1) fun _ => noA_pure _

theorem noA_q2LocalRound (q : Nat) (str : List Nat) (value : S2) : NoA (q2LocalRound q str value) :=
  noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Add _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
  noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ => noA_pure _

theorem noA_q2LocalRounds (str : List Nat) : ∀ (k q : Nat) (value : S2), NoA (q2LocalRounds str k q value)
  | 0, _, _ => noA_pure _
  | k + 1, q, value => noA_bind (noA_q2LocalRound q str value) fun a =>
    noA_bind (noA_q2LocalRounds str k (q + 16) a.1) fun _ => noA_pure _

/-! ## Walking an `E2` template -/

/-- `TInv` on `THold2`: the rows of the rest `R` hold (twin rows included), the whole has length `L`, and the
whole's assertions `TA` hold iff the rest's do and `Q`. -/
def TInv2 (xv : Src → FE) (V : Nat → FE) (TA : Prop) (L : Nat) (Q : Prop) {α : Type} (R : TB α) (n : Nat) :
    Prop :=
  THold2 xv V n (R n).2 ∧ L = n + (R n).2.length ∧ (TA ↔ TAssert xv V (R n).2 ∧ Q)

theorem inv_start2 {xv : Src → FE} {V : Nat → FE} {α : Type} {R : TB α} (h : THold2 xv V 0 (R 0).2) :
    TInv2 xv V (TAssert xv V (R 0).2) (R 0).2.length True R 0 :=
  ⟨h, (Nat.zero_add _).symm, ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩⟩

/-- Read a gadget without assertions. -/
theorem peelN2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv2 xv V TA L Q (m >>= f) n) (hm : NoA m) :
    ∃ a n', (m n).1 = a ∧ THold2 xv V n (m n).2 ∧ TInv2 xv V TA L Q (f a) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold2_bind] at h1
  refine ⟨(m n).1, n + (m n).2.length, rfl, h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

/-- Read the last gadget (its position kept). -/
theorem peelL2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv2 xv V TA L Q (m >>= f) n) (hm : NoA m) :
    THold2 xv V n (m n).2 ∧ TInv2 xv V TA L Q (f (m n).1) (n + (m n).2.length) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold2_bind] at h1
  refine ⟨h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

theorem tassert_q2Assert {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : S2} {g : Src} :
    TAssert xv V (q2Assert a g n).2 ↔ g.valF xv V * a.1.valF xv V = 0 ∧ g.valF xv V * a.2.valF xv V = 0 := by
  refine ⟨q2Assert_spec, fun ⟨h1, h2⟩ => (tassert_bind _ _).mpr ⟨tassert_gAssert.mpr h1, tassert_gAssert.mpr h2⟩⟩

/-- Read a coordinatewise assertion. -/
theorem peelA2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {β : Type} {a : S2} {g : Src}
    {f : Unit → TB β} {n : Nat} (h : TInv2 xv V TA L Q (q2Assert a g >>= f) n) :
    ∃ n', TInv2 xv V TA L (Q ∧ (g.valF xv V * a.1.valF xv V = 0 ∧ g.valF xv V * a.2.valF xv V = 0)) (f ()) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (q2Assert a g n).1 = () := rfl
  rw [thold2_bind, e] at h1
  rw [tb_bind, e] at h2
  rw [tassert_bind, e] at h3
  refine ⟨n + (q2Assert a g n).2.length, h1.2, ?_, ?_⟩
  · rw [h2, List.length_append]; omega
  · rw [h3, tassert_q2Assert]
    exact ⟨fun ⟨⟨h, h'⟩, hq⟩ => ⟨h', hq, h⟩, fun ⟨h', hq, h⟩ => ⟨⟨h, h'⟩, hq⟩⟩

theorem inv_end2 {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {n : Nat}
    (h : TInv2 xv V TA L Q (pure () : TB Unit) n) : L = n ∧ (TA ↔ Q) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨by simpa [tb_pure] using h2, ?_⟩
  rw [h3]
  exact ⟨fun h => h.2, fun h => ⟨noA_pure () xv V n, h⟩⟩

/-- An `E2` value is `0` iff both coordinates are. -/
theorem s2_zero_iff {xv : Src → FE} {V : Nat → FE} (a : S2) :
    a.valF xv V = 0 ↔ (a.1.valF xv V).c₀ = 0 ∧ (a.2.valF xv V).c₀ = 0 := by
  constructor
  · intro h
    exact ⟨congrArg FE2.re h, congrArg FE2.im h⟩
  · rintro ⟨h1, h2⟩
    show (⟨(a.1.valF xv V).c₀, (a.2.valF xv V).c₀⟩ : FE2) = ⟨0, 0⟩
    rw [h1, h2]

/-! ## Copy rows -/

theorem mapT2_q2Copy_fst : ∀ (l : List S2) (n : Nat), (mapT2 q2Copy l n).1 =
    (List.range l.length).map fun j => ((.loc (n + 2 * j), .loc (n + 2 * j + 1)) : S2)
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapT2, tb_bind, tb_pure, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [mapT2_q2Copy_fst as]
    simp only [Function.comp_def, q2Copy, q2Lin, emit2, e2I, List.length_cons, List.length_nil, Nat.mul_zero,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    congr 2 <;> omega

theorem mapT2_q2Copy_length (l : List S2) (n : Nat) : (mapT2 q2Copy l n).2.length = 2 * l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons a as ih =>
    simp only [mapT2, tb_bind, tb_pure, List.append_nil, List.length_append, ih, List.length_cons]
    simp only [q2Copy, q2Lin, emit2, e2I, List.length_cons, List.length_nil]
    omega

/-- **The copy rows**: value `j` of `l` sits in the twin cells `n + 2j`, `n + 2j + 1`. -/
theorem cp2_get {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List S2} (h : THold2 xv V n (mapT2 q2Copy l n).2) :
    ∀ j < l.length, (⟨(V (n + 2 * j)).c₀, (V (n + 2 * j + 1)).c₀⟩ : FE2) = (vals2 xv V l).getD j 0 := by
  intro j hj
  have k := mapT2_spec (P := fun a s => S2.valF xv V s = a.valF xv V) (fun a m hm => q2Copy_spec hm) l n h
  have e := forall₂_map_eq2 k
  rw [mapT2_q2Copy_fst] at e
  have := congrArg (fun L : List FE2 => L.getD j 0) e
  simp only [List.map_map, Function.comp_def] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range] at this
  rw [← this]
  rfl

end Lvm.Q1
