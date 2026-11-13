-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): Q_arith's gadgets for the child's shape:
-- the shape cell `σ'`, muxes, `D`'s and the ring's small claims with their tails, and the regular claims'
-- term pairs (big and moved keys sharing their leaf). Built on HAR-WH's batching (`LvmQAsmArith2WhirBasis*`:
-- `chainG`, `ringLeaf`, `partW_eq`, `kprod_keyOf`, `trieG`).
import LvmQShapeF

/-!
# The child's shape in Q_arith: gadgets

* **`muxG s a b`**: `s (a + b) + a` (two rows): `a` when `s = 0`, `b` when `s = 1`.
* **`zsumG a b`**: `Σ_l eq((a, b), l) · z*_l` (four rows; `zF`), the `D` tail's lane factor.
* **`dClaimG`**: a `D` point claim `⟨22, 0⟩` at `z` as the muxed claim `sum ν [(κ_m, ⟨22, 0⟩, z_m)]` (`ν = CMain.nu20`)
  (`κ_m = 1`, `z_m = z` when `s = 0`; `κ`, `dzD z` when `s = 1`), its value `v + s · t`,
  `t = (1 + κ) · zF(z₂₀, z₂₁)` (`tailD`).
* **`ringClaimG`**: the tape's ring claim on `⟨ν, 0⟩` as the muxed ring claim (`ptZ`, `csZ` when `s = 1`), its value
  `v + s · t`, `t = Σ_k c_k (1 + κ(pt^{2^k})) · zF(pt₂₀^{2^k}, pt₂₁^{2^k})` (`tailR`).
* **`zClaimG`**: per claim: `D`'s and the ring's muxed, every other claim kept and flagged regular.
-/

set_option autoImplicit false

namespace Lvm.QShape

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Shape

variable {c : Ctx} {M : Mem}

/-! ## Muxes -/

/-- `s (a + b) + a`. -/
def mux (s a b : FE) : FE := s * (a + b) + a

theorem mux_zero (a b : FE) : mux 0 a b = a := by simp [mux]
theorem mux_one (a b : FE) : mux 1 a b = b := by
  simp only [mux, one_mul]; rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **The mux**: `a` when `s = 0`, `b` when `s = 1`. -/
def muxG (s a b : Cell) : BM Cell := do
  let u ← lin .E 1 0 a b
  mulAdd .E s u a

theorem muxG_spec (s a b : Cell) : Hs c M (muxG s a b) (fun r ↦ r.val M = mux (s.val M) (a.val M) (b.val M)) :=
  hs_bind (hs_lin _ _ _ _ _) fun u hu ↦ hs_mono (hs_mulAdd _ _ _ _) fun r hr ↦ by
    rw [hr, hu, ofK_one, ofK_zero, one_mul, add_zero, mux]

/-- `1 + a`. -/
def onePlusG (a : Cell) : BM Cell := lin .E 0 1 a a

theorem onePlusG_spec (a : Cell) : Hs c M (onePlusG a) (fun r ↦ r.val M = 1 + a.val M) :=
  hs_mono (hs_lin _ _ _ _ _) fun r hr ↦ by rw [hr, ofK_zero, ofK_one, zero_mul, add_zero, add_comm]

/-! ## `z*` as constants -/

/-- `z*_l` as a base-field constant. -/
def zK (l : ℕ) : FK := ⟨(LeanVM.Semantics.keccakF1600 (Vector.replicate 25 0)).toArray.getD l 0⟩

theorem ofK_zK (l : ℕ) : FE.ofK (zK l) = zStarF l := by
  unfold zK zStarF zStarsF
  simp [Array.getD]
  split <;> rfl

/-- The lane factor of a `D` tail: `Σ_l eq((a, b), l) · z*_l`. -/
def zF (a b : FE) : FE := ((List.range 4).map fun l ↦ eqEval [a, b] (selectorPoint l 2) * zStarF l).sum

/-- **`zF` in four rows** (`z` holds `0`). -/
def zsumG (a b z : Cell) : BM Cell := do
  let ab ← mulAdd .E a b z
  let u1 ← lin .E (zK 0 + zK 1) (zK 0) z a
  let u2 ← lin .E (zK 0 + zK 2) 0 u1 b
  lin .E (zK 0 + zK 1 + zK 2 + zK 3) 0 u2 ab

theorem zF_eq (a b : FE) : zF a b = zStarF 0 + (zStarF 0 + zStarF 1) * a + (zStarF 0 + zStarF 2) * b +
    (zStarF 0 + zStarF 1 + zStarF 2 + zStarF 3) * (a * b) := by
  simp only [zF, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.map_append,
    List.sum_append, List.sum_cons, List.sum_nil, selectorPoint, eqEval]
  norm_num [eOfNat_zero, eOfNat_one]
  linear_combination (zStarF 1 * (1 + b) + zStarF 2 * (1 + a) + zStarF 3 * (a + b) + 2 * zStarF 3) *
    (CharTwo.two_eq_zero : (2 : FE) = 0)

theorem zsumG_spec {a b z : Cell} (hz : z.val M = 0) :
    Hs c M (zsumG a b z) (fun r ↦ r.val M = zF (a.val M) (b.val M)) :=
  hs_bind (hs_mulAdd _ _ _ _) fun ab hab ↦ hs_bind (hs_lin _ _ _ _ _) fun u1 hu1 ↦
    hs_bind (hs_lin _ _ _ _ _) fun u2 hu2 ↦ hs_mono (hs_lin _ _ _ _ _) fun r hr ↦ by
      rw [hr, hu2, hu1, hab, hz, zF_eq]
      simp only [ofK_add, ofK_zero, ofK_zK]
      ring

/-! ## `D`'s point claims -/

/-- `D`'s tail in closed form: `(1 + κ(z)) · zF(z₂₀, z₂₁)`. -/
def tailD (z : List FE) : FE := (1 + kappaD z) * zF (z.getD 20 0) (z.getD 21 0)

/-- **A `D` point claim, muxed** (`zl` the 22 point cells, `s` the shape cell). -/
def dClaimG (s z o : Cell) (cc : CClaim) (zl : List Cell) : BM CClaim := do
  let a ← onePlusG (zl.getD 18 default)
  let b ← onePlusG (zl.getD 19 default)
  let κ ← mulAdd .E a b z
  let κm ← muxG s o κ
  let m18 ← muxG s (zl.getD 18 default) (zl.getD 20 default)
  let m19 ← muxG s (zl.getD 19 default) (zl.getD 21 default)
  let m20 ← muxG s (zl.getD 20 default) z
  let m21 ← muxG s (zl.getD 21 default) z
  let zv ← zsumG (zl.getD 20 default) (zl.getD 21 default) z
  let u ← onePlusG κ
  let t ← mulAdd .E u zv z
  let v' ← mulAdd .E s t cc.value
  pure ⟨cc.com, .sum CMain.nu20 [(κm, ⟨22, 0⟩, zl.take 18 ++ [m18, m19, m20, m21])], v'⟩

/-- What `dClaimG`'s output is: the muxed scale and point cells' values, the value cell's. -/
structure DOut (M : Mem) (s z : Cell) (cc : CClaim) (zl : List Cell) (r : CClaim) : Prop where
  com : r.com = cc.com
  form : ∃ κm m18 m19 m20 m21 : Cell, r.cw = .sum CMain.nu20 [(κm, ⟨22, 0⟩, zl.take 18 ++ [m18, m19, m20, m21])] ∧
    κm.val M = mux (s.val M) 1 (kappaD (vs M zl)) ∧
    m18.val M = mux (s.val M) ((vs M zl).getD 18 0) ((vs M zl).getD 20 0) ∧
    m19.val M = mux (s.val M) ((vs M zl).getD 19 0) ((vs M zl).getD 21 0) ∧
    m20.val M = mux (s.val M) ((vs M zl).getD 20 0) 0 ∧
    m21.val M = mux (s.val M) ((vs M zl).getD 21 0) 0
  value : r.value.val M = cc.value.val M + s.val M * tailD (vs M zl)

theorem vs_getD' (l : List Cell) (i : ℕ) (hi : i < l.length) : (l.getD i default).val M = (vs M l).getD i 0 := by
  simp [vs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem dClaimG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (cc : CClaim) (zl : List Cell)
    (hzl : zl.length = 22) : Hs c M (dClaimG s z o cc zl) (DOut M s z cc zl) := by
  have g : ∀ i < 22, (zl.getD i default).val M = (vs M zl).getD i 0 := fun i hi ↦ vs_getD' zl i (by omega)
  unfold dClaimG
  refine hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
    hs_bind (hs_mulAdd _ _ _ _) fun κ hκ ↦ hs_bind (muxG_spec _ _ _) fun κm hκm ↦
    hs_bind (muxG_spec _ _ _) fun m18 h18 ↦ hs_bind (muxG_spec _ _ _) fun m19 h19 ↦
    hs_bind (muxG_spec _ _ _) fun m20 h20 ↦ hs_bind (muxG_spec _ _ _) fun m21 h21 ↦
    hs_bind (zsumG_spec hz) fun zv hzv ↦ hs_bind (onePlusG_spec _) fun u hu ↦
    hs_bind (hs_mulAdd _ _ _ _) fun t ht ↦ hs_bind (hs_mulAdd _ _ _ _) fun v' hv' ↦ hs_pure ⟨rfl, ?_, ?_⟩
  · have hk : κ.val M = kappaD (vs M zl) := by
      rw [hκ, ha, hb, hz, add_zero, kappaD, g 18 (by norm_num), g 19 (by norm_num)]
    refine ⟨κm, m18, m19, m20, m21, rfl, by rw [hκm, ho, hk], ?_, ?_, ?_, ?_⟩
    · rw [h18, g 18 (by norm_num), g 20 (by norm_num)]
    · rw [h19, g 19 (by norm_num), g 21 (by norm_num)]
    · rw [h20, g 20 (by norm_num), hz]
    · rw [h21, g 21 (by norm_num), hz]
  · show v'.val M = _
    rw [hv', ht, hu, hzv, hκ, ha, hb, hz, add_zero, add_zero, tailD, kappaD, g 18 (by norm_num),
      g 19 (by norm_num), g 20 (by norm_num), g 21 (by norm_num)]
    ring

/-! ## The tape's ring claim -/

/-- The ring's tail in closed form: `Σ_k c_k (1 + κ(pt^{2^k})) · zF(pt₂₀^{2^k}, pt₂₁^{2^k})`. -/
def tailR (pt cs : List FE) : FE :=
  ∑ k ∈ Finset.range cs.length, cs.getD k 0 * ((1 + kappaD (pt.map (· ^ 2 ^ k))) *
    zF ((pt.getD 20 0) ^ 2 ^ k) ((pt.getD 21 0) ^ 2 ^ k))

/-- One coefficient per step: `c'_k = mux(s, c_k, c_k κ_k)`, the tail's running sum, the squares. -/
def ringStepG (s z : Cell) : List Cell → Cell → Cell → Cell → Cell → Cell → BM (List Cell × Cell)
  | [], _, _, _, _, acc => pure ([], acc)
  | c :: cs, r18, r19, r20, r21, acc => do
    let a ← onePlusG r18
    let b ← onePlusG r19
    let m ← mulAdd .E a b z
    let c' ← mulAdd .E c m z
    let cm ← muxG s c c'
    let zv ← zsumG r20 r21 z
    let u ← onePlusG m
    let w ← mulAdd .E u zv z
    let acc' ← mulAdd .E c w acc
    let q18 ← mulAdd .E r18 r18 z
    let q19 ← mulAdd .E r19 r19 z
    let q20 ← mulAdd .E r20 r20 z
    let q21 ← mulAdd .E r21 r21 z
    let rest ← ringStepG s z cs q18 q19 q20 q21 acc'
    pure (cm :: rest.1, rest.2)

theorem ringStepG_spec {s z : Cell} (hz : z.val M = 0) (P : List FE) :
    ∀ (cs : List Cell) (k : ℕ) (r18 r19 r20 r21 acc : Cell),
      r18.val M = (P.getD 18 0) ^ 2 ^ k → r19.val M = (P.getD 19 0) ^ 2 ^ k →
      r20.val M = (P.getD 20 0) ^ 2 ^ k → r21.val M = (P.getD 21 0) ^ 2 ^ k →
      Hs c M (ringStepG s z cs r18 r19 r20 r21 acc) (fun r ↦ r.1.length = cs.length ∧
        (∀ j < cs.length, (r.1.getD j default).val M = mux (s.val M) ((vs M cs).getD j 0)
          ((vs M cs).getD j 0 * ((1 + (P.getD 18 0) ^ 2 ^ (k + j)) * (1 + (P.getD 19 0) ^ 2 ^ (k + j))))) ∧
        r.2.val M = acc.val M + ∑ j ∈ Finset.range cs.length, (vs M cs).getD j 0 *
          ((1 + (1 + (P.getD 18 0) ^ 2 ^ (k + j)) * (1 + (P.getD 19 0) ^ 2 ^ (k + j))) *
            zF ((P.getD 20 0) ^ 2 ^ (k + j)) ((P.getD 21 0) ^ 2 ^ (k + j))))
  | [], _, _, _, _, _, acc, _, _, _, _ => hs_pure ⟨rfl, fun j hj ↦ absurd hj (by simp), by simp⟩
  | cc :: cs, k, r18, r19, r20, r21, acc, h18, h19, h20, h21 => by
    unfold ringStepG
    have sq : ∀ (x : FE) (k : ℕ), (x ^ 2 ^ k) * (x ^ 2 ^ k) = x ^ 2 ^ (k + 1) := fun x k ↦ by
      rw [← pow_add, pow_succ]; ring_nf
    refine hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
      hs_bind (hs_mulAdd _ _ _ _) fun m hm ↦ hs_bind (hs_mulAdd _ _ _ _) fun c' hc' ↦
      hs_bind (muxG_spec _ _ _) fun cm hcm ↦ hs_bind (zsumG_spec hz) fun zv hzv ↦
      hs_bind (onePlusG_spec _) fun u hu ↦ hs_bind (hs_mulAdd _ _ _ _) fun w hw ↦
      hs_bind (hs_mulAdd _ _ _ _) fun acc' hacc ↦ hs_bind (hs_mulAdd _ _ _ _) fun q18 hq18 ↦
      hs_bind (hs_mulAdd _ _ _ _) fun q19 hq19 ↦ hs_bind (hs_mulAdd _ _ _ _) fun q20 hq20 ↦
      hs_bind (hs_mulAdd _ _ _ _) fun q21 hq21 ↦ hs_bind (ringStepG_spec hz P cs (k + 1) q18 q19 q20 q21 acc'
        (by rw [hq18, h18, hz, add_zero, sq]) (by rw [hq19, h19, hz, add_zero, sq])
        (by rw [hq20, h20, hz, add_zero, sq]) (by rw [hq21, h21, hz, add_zero, sq])) fun rest ⟨hl, hv, ht⟩ ↦
      hs_pure ⟨by simp [hl], fun j hj ↦ ?_, ?_⟩
    · rcases j with _ | j
      · simp only [List.getD_cons_zero, vs, List.map_cons, Nat.add_zero]
        rw [hcm, hc', hm, ha, hb, hz, add_zero, add_zero, h18, h19]
      · simp only [List.getD_cons_succ, vs, List.map_cons, List.length_cons] at hj ⊢
        rw [hv j (by omega), show k + (j + 1) = k + 1 + j by omega]
        rfl
    · rw [ht, hacc, hw, hu, hm, ha, hb, hzv, hz, add_zero, add_zero, h18, h19, h20, h21, List.length_cons,
        Finset.sum_range_succ', add_assoc]
      have e : ∀ j, k + (j + 1) = k + 1 + j := fun j ↦ by omega
      simp only [Nat.add_assoc, Nat.add_comm 1] at ht ⊢
      simp only [vs, List.map_cons, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      ring

/-- **The tape's ring claim, muxed** (`pt` `ν` point cells with `pt₂₂ … = z`, the block bits above `D`, `cs` 64
coefficients). -/
def ringClaimG (s z : Cell) (cc : CClaim) (pt cs : List Cell) : BM CClaim := do
  let r ← ringStepG s z cs (pt.getD 18 default) (pt.getD 19 default) (pt.getD 20 default) (pt.getD 21 default) z
  let m18 ← muxG s (pt.getD 18 default) (pt.getD 20 default)
  let m19 ← muxG s (pt.getD 19 default) (pt.getD 21 default)
  let m20 ← muxG s (pt.getD 20 default) z
  let m21 ← muxG s (pt.getD 21 default) z
  let v' ← mulAdd .E s r.2 cc.value
  pure ⟨cc.com, .ring ⟨CMain.nu20, 0⟩ (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) r.1, v'⟩

theorem kappaD_map (P : List FE) (k : ℕ) (hP : P.length = CMain.nu20) :
    kappaD (P.map (· ^ 2 ^ k)) = (1 + (P.getD 18 0) ^ 2 ^ k) * (1 + (P.getD 19 0) ^ 2 ^ k) := by
  have h18 : 18 < P.length := by rw [hP]; decide
  have h19 : 19 < P.length := by rw [hP]; decide
  simp [kappaD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h18,
    List.getElem?_eq_getElem h19]

/-- What `ringClaimG`'s output is. -/
structure ROut (M : Mem) (s z : Cell) (cc : CClaim) (pt cs : List Cell) (r : CClaim) : Prop where
  com : r.com = cc.com
  form : ∃ m18 m19 m20 m21 : Cell, ∃ csm : List Cell,
    r.cw = .ring ⟨CMain.nu20, 0⟩ (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) csm ∧
    m18.val M = mux (s.val M) ((vs M pt).getD 18 0) ((vs M pt).getD 20 0) ∧
    m19.val M = mux (s.val M) ((vs M pt).getD 19 0) ((vs M pt).getD 21 0) ∧
    m20.val M = mux (s.val M) ((vs M pt).getD 20 0) 0 ∧
    m21.val M = mux (s.val M) ((vs M pt).getD 21 0) 0 ∧
    csm.length = cs.length ∧
    ∀ j < cs.length, (csm.getD j default).val M =
      mux (s.val M) ((vs M cs).getD j 0) ((csZ (vs M pt) (vs M cs)).getD j 0)
  value : r.value.val M = cc.value.val M + s.val M * tailR (vs M pt) (vs M cs)

theorem ringClaimG_spec {s z : Cell} (hz : z.val M = 0) (cc : CClaim) (pt cs : List Cell)
    (hpt : pt.length = CMain.nu20) :
    Hs c M (ringClaimG s z cc pt cs) (ROut M s z cc pt cs) := by
  have g : ∀ i < CMain.nu20, (pt.getD i default).val M = (vs M pt).getD i 0 := fun i hi ↦ vs_getD' pt i (by omega)
  have hP : (vs M pt).length = CMain.nu20 := by simp [vs, hpt]
  unfold ringClaimG
  refine hs_bind (ringStepG_spec hz (vs M pt) cs 0 _ _ _ _ z (by rw [g 18 (by norm_num)]; simp)
      (by rw [g 19 (by norm_num)]; simp) (by rw [g 20 (by norm_num)]; simp) (by rw [g 21 (by norm_num)]; simp))
    fun r ⟨hl, hv, ht⟩ ↦ hs_bind (muxG_spec _ _ _) fun m18 h18 ↦ hs_bind (muxG_spec _ _ _) fun m19 h19 ↦
    hs_bind (muxG_spec _ _ _) fun m20 h20 ↦ hs_bind (muxG_spec _ _ _) fun m21 h21 ↦
    hs_bind (hs_mulAdd _ _ _ _) fun v' hv' ↦ hs_pure ⟨rfl, ⟨m18, m19, m20, m21, r.1, rfl, ?_, ?_, ?_, ?_, hl, ?_⟩, ?_⟩
  · rw [h18, g 18 (by norm_num), g 20 (by norm_num)]
  · rw [h19, g 19 (by norm_num), g 21 (by norm_num)]
  · rw [h20, g 20 (by norm_num), hz]
  · rw [h21, g 21 (by norm_num), hz]
  · intro j hj
    rw [hv j hj, Nat.zero_add]
    congr 1
    have hj' : j < (vs M cs).length := by simp [vs]; exact hj
    simp [csZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj', kappaD_map _ _ hP]
  · show v'.val M = _
    rw [hv', ht, hz, zero_add, tailR]
    have hcl : (vs M cs).length = cs.length := by simp [vs]
    rw [hcl]
    simp only [Nat.zero_add, kappaD_map _ _ hP]
    ring

/-! ## Claims in both shapes -/

/-- **The static form of `C_main`'s claims** (decided on the record; `ν = CMain.nu20`): a `D` point claim
(`⟨22, 0⟩`, 22 cells), the tape's ring claim (`⟨ν, 0⟩`, `ν` point cells ending in `ν − 22` zero cells, the block
bits above `D`, 64 coefficients), or a regular claim (point/ring on a regular block, `sum ν` of regular parts). -/
def ZWF (z : Cell) (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then decide (zl.length = 22) else decide (RegP blk)
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then decide (pt.length = CMain.nu20) &&
      (pt.drop 22).all (· == z) && decide (cs.length = 64) else decide (RegP blk)
  | .sum nu parts => decide (nu = CMain.nu20) && parts.all fun e ↦ decide (RegP e.2.1)

/-- **One claim in both shapes**: `D`'s and the ring's muxed (flag `false`), every other kept (flag `true`:
its small form is the moved claim, built as moved keys over the same leaves). -/
def zClaimG (s z o : Cell) (cc : CClaim) : BM (CClaim × Bool) :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then do let r ← dClaimG s z o cc zl; pure (r, false) else pure (cc, true)
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then do let r ← ringClaimG s z cc pt cs; pure (r, false)
      else pure (cc, true)
  | .sum _ _ => pure (cc, true)

/-- The claims in both shapes. -/
def zClaimsG (s z o : Cell) : List CClaim → BM (List (CClaim × Bool))
  | [] => pure []
  | cc :: cl => do
    let r ← zClaimG s z o cc
    let rs ← zClaimsG s z o cl
    pure (r :: rs)

/-- The tail value of a claim (the cells' closed form): `tailD` for `D`, `tailR` for the ring, `0` else. -/
def tailC (M : Mem) (cc : CClaim) : FE :=
  match cc.cw with
  | .point blk zl => if blk = ⟨22, 0⟩ then tailD (vs M zl) else 0
  | .ring blk pt cs => if blk = ⟨CMain.nu20, 0⟩ then tailR (vs M pt) (vs M cs) else 0
  | .sum _ _ => 0

/-- A regular claim: its blocks (every part's) regular. -/
def RegC (cc : CClaim) : Prop :=
  match cc.cw with
  | .point blk _ => RegP blk
  | .ring blk _ _ => RegP blk
  | .sum nu parts => nu = CMain.nu20 ∧ ∀ e ∈ parts, RegP e.2.1

/-- The small form of a regular claim: its blocks moved down. -/
def smallW (M : Mem) (cc : CClaim) : List FE → FE :=
  match cc.cw with
  | .point blk zl => (BlockClaim.point (shiftP blk) (vs M zl) 0).onStack.1
  | .ring blk pt cs => (⟨shiftP blk, fun y ↦ ringWeight (vs M pt) y (vs M cs), 0⟩ : BlockClaim).onStack.1
  | .sum nu parts => (sumClaim nu (parts.map fun e ↦ (e.1.val M, shiftP e.2.1, vs M e.2.2)) 0).onStack.1

/-! ## One claim in both shapes: the relation -/

theorem list_ext_getD (l l' : List FE) (h : l.length = l'.length) (hg : ∀ j < l.length, l.getD j 0 = l'.getD j 0) :
    l = l' :=
  List.ext_getElem h fun j h1 h2 ↦ by
    have := hg j h1
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem onStack_val_irrel (b : Placement) (w : List FE → FE) (v v' : FE) :
    (⟨b, w, v⟩ : BlockClaim).onStack.1 = (⟨b, w, v'⟩ : BlockClaim).onStack.1 := rfl

theorem take_getD4 (l : List FE) (hl : l.length = 22) :
    l.take 18 ++ [l.getD 18 0, l.getD 19 0, l.getD 20 0, l.getD 21 0] = l := by
  obtain ⟨zl, a, b, c, d, rfl, h⟩ := split4 l 18 (by omega)
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h, List.take_append_of_le_length]

theorem take_getD_nu (l : List FE) (hl : l.length = CMain.nu20) :
    l.take 18 ++ [l.getD 18 0, l.getD 19 0, l.getD 20 0, l.getD 21 0] ++ l.drop 22 = l := by
  have h := take_getD4 (l.take 22) (by simp only [List.length_take, hl]; decide)
  rw [List.take_take, min_eq_left (by norm_num), getD_take' _ _ (by norm_num : 18 < 22),
    getD_take' _ _ (by norm_num : 19 < 22), getD_take' _ _ (by norm_num : 20 < 22),
    getD_take' _ _ (by norm_num : 21 < 22)] at h
  conv_rhs => rw [← List.take_append_drop 22 l, ← h]

/-- The two values a shape cell can hold. -/
def IsBit (a : FE) : Prop := a = 0 ∨ a = 1

/-- **What `zClaimG` gives** for a claim `cc` of the static form (`ZWF`), at any point `x` of `ν` coordinates:
the same commitment; the value `v + s · tail`; the big form when `s = 0`; when `s = 1`, the small form at `x^σ`
is `V_S`'s small claim `onStackZB` at `x` (a regular claim's small form is `smallW`, its blocks moved). -/
structure ZRel (M : Mem) (s : Cell) (cc : CClaim) (r : CClaim × Bool) : Prop where
  com : r.1.com = cc.com
  value : r.1.value.val M = cc.value.val M + s.val M * tailC M cc
  reg : r.2 = true → r.1 = cc
  regC : r.2 = true → RegC cc
  big : r.2 = false → s.val M = 0 → ∀ x : List FE, x.length = CMain.nu20 →
    (r.1.val M).2.onStack.1 x = (cc.val M).2.onStack.1 x
  small : s.val M = 1 → ∀ x : List FE, x.length = CMain.nu20 →
    (if r.2 then smallW M cc (rotZ x) else (r.1.val M).2.onStack.1 (rotZ x)) =
      (onStackZB (cc.val M).2 (tailC M cc)).1 x
  wf : WF1 CMain.nu20 cc = true → WF1 CMain.nu20 r.1 = true

theorem rotZ_length (x : List FE) (hx : x.length = CMain.nu20) : (rotZ x).length = CMain.nu20 := by
  cases x with
  | nil => simp at hx
  | cons x0 xt => simp [rotZ]; simpa using hx

theorem zClaimG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (cc : CClaim) (hw : ZWF z cc = true) :
    Hs c M (zClaimG s z o cc) (ZRel M s cc) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    by_cases hb : blk = ⟨22, 0⟩
    · subst hb
      have hzl : zl.length = 22 := by simpa [ZWF] using hw
      simp only [zClaimG, if_pos rfl]
      refine hs_bind (dClaimG_spec hz ho _ zl hzl) fun r hr ↦ hs_pure ?_
      obtain ⟨hcom, ⟨κm, m18, m19, m20, m21, hcw, hκ, h18, h19, h20, h21⟩, hval⟩ := hr
      have hvl : (vs M zl).length = 22 := by simp [vs, hzl]
      have e : ∀ x : List FE, x.length = CMain.nu20 → (r.val M).2.onStack.1 x = κm.val M * (BlockClaim.point ⟨22, 0⟩
          ((vs M zl).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M]) 0).onStack.1 x := by
        intro x hx
        rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [CClaim.val]
        rw [sumClaim_onStack _ _ _ hx]
        simp [vs, List.map_take, partB, BlockClaim.point, BlockClaim.onStack]
      have tc : tailC M ⟨com, .point ⟨22, 0⟩ zl, v⟩ = tailD (vs M zl) := by simp [tailC]
      refine ⟨hcom, by rw [hval, tc], fun h ↦ absurd h (by simp), fun h ↦ absurd h (by simp), fun _ hs x hx ↦ ?_, fun hs x hx ↦ ?_, fun _ ↦ ?_⟩
      · rw [e x hx, hκ, h18, h19, h20, h21, hs, mux_zero, mux_zero, mux_zero, mux_zero, mux_zero, one_mul,
          take_getD4 _ hvl]
        rfl
      · simp only [Bool.false_eq_true, if_false]
        rw [e _ (rotZ_length x hx), hκ, h18, h19, h20, h21, hs, mux_one, mux_one, mux_one, mux_one, mux_one, tc]
        exact (onStackZB_dpt (vs M zl) hvl (v.val M) _ x hx).symm
      · rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp [WF1, hzl, CMain.nu20]
    · have hr : RegP blk := by simpa [ZWF, hb] using hw
      have tc : tailC M ⟨com, .point blk zl, v⟩ = 0 := by simp [tailC, hb]
      simp only [zClaimG, if_neg hb]
      refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ hr, fun h ↦ absurd h (by simp),
        fun _ x hx ↦ ?_, fun h ↦ h⟩
      simp only [if_true, tc]
      rw [onStackZB_reg _ 0 hr x hx]
      rfl
  | ring blk pt cs =>
    by_cases hb : blk = ⟨CMain.nu20, 0⟩
    · subst hb
      have hw' : pt.length = CMain.nu20 ∧ (∀ x ∈ pt.drop 22, x = z) ∧ cs.length = 64 := by
        simpa [ZWF, and_assoc] using hw
      obtain ⟨hpt, h22, hcs⟩ := hw'
      simp only [zClaimG, if_pos rfl]
      refine hs_bind (ringClaimG_spec hz _ pt cs hpt) fun r hr ↦ hs_pure ?_
      obtain ⟨hcom, ⟨m18, m19, m20, m21, csm, hcw, h18', h19', h20', h21', hcl, hcv⟩, hval⟩ := hr
      have hP : (vs M pt).length = CMain.nu20 := by simp [vs, hpt]
      have hP0 : (vs M pt).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp [vs, hpt], fun b hb ↦ ?_⟩
        rw [vs, ← List.map_drop] at hb
        obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hb
        rw [h22 x' hx', hz]
      have epm : vs M (pt.take 18 ++ [m18, m19, m20, m21] ++ pt.drop 22) =
          (vs M pt).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M] ++ (vs M pt).drop 22 := by
        simp [vs, List.map_take, List.map_drop]
      have e : ∀ x : List FE, (r.val M).2.onStack.1 x =
          (⟨⟨CMain.nu20, 0⟩, fun y ↦ ringWeight ((vs M pt).take 18 ++ [m18.val M, m19.val M, m20.val M, m21.val M] ++
            (vs M pt).drop 22) y (vs M csm), 0⟩ : BlockClaim).onStack.1 x := by
        intro x
        rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [CClaim.val, epm]
        rfl
      have tc : tailC M ⟨com, .ring ⟨CMain.nu20, 0⟩ pt cs, v⟩ = tailR (vs M pt) (vs M cs) := by simp [tailC]
      have hcsl : (vs M csm).length = (vs M cs).length := by simp [vs, hcl]
      refine ⟨hcom, by rw [hval, tc], fun h ↦ absurd h (by simp), fun h ↦ absurd h (by simp), fun _ hs x hx ↦ ?_, fun hs x hx ↦ ?_, fun hwf ↦ ?_⟩
      · rw [e x, h18', h19', h20', h21', hs, mux_zero, mux_zero, mux_zero, mux_zero, take_getD_nu _ hP]
        have ec : vs M csm = vs M cs := list_ext_getD _ _ hcsl fun j hj ↦ by
          rw [← vs_getD' csm j (by simpa [vs] using hj), hcv j (by simpa [vs, hcl] using hj), hs, mux_zero]
        rw [ec]
        rfl
      · simp only [Bool.false_eq_true, if_false]
        rw [e _, h18', h19', h20', h21', hs, mux_one, mux_one, mux_one, mux_one, tc]
        have ep : (vs M pt).take 18 ++ [(vs M pt).getD 20 0, (vs M pt).getD 21 0, 0, 0] ++ (vs M pt).drop 22 =
            ptZ (vs M pt) := by
          rw [hP0]; rfl
        have ec : vs M csm = csZ (vs M pt) (vs M cs) := list_ext_getD _ _ (by rw [hcsl]; simp [csZ, vs]) fun j hj ↦ by
          rw [← vs_getD' csm j (by simpa [vs] using hj), hcv j (by simpa [vs, hcl] using hj), hs, mux_one]
        rw [ep, ec]
        exact (onStackZB_ring (vs M pt) (vs M cs) hP hP0 (v.val M) _ x hx).symm
      · rcases r with ⟨rc, rw, rv⟩
        simp only at hcw
        subst hcw
        simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf ⊢
        refine ⟨⟨⟨hwf.1.1.1, by simp [hpt, CMain.nu20]⟩, by rw [hcl]; exact hwf.1.2⟩, hwf.2⟩
    · have hr : RegP blk := by simpa [ZWF, hb] using hw
      have tc : tailC M ⟨com, .ring blk pt cs, v⟩ = 0 := by simp [tailC, hb]
      simp only [zClaimG, if_neg hb]
      refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ hr, fun h ↦ absurd h (by simp),
        fun _ x hx ↦ ?_, fun h ↦ h⟩
      simp only [if_true, tc]
      rw [onStackZB_reg _ 0 hr x hx]
      rfl
  | sum nu parts =>
    have hw' : nu = CMain.nu20 ∧ ∀ e ∈ parts, RegP e.2.1 := by simpa [ZWF] using hw
    obtain ⟨rfl, hp⟩ := hw'
    have tc : tailC M ⟨com, .sum CMain.nu20 parts, v⟩ = 0 := by simp [tailC]
    refine hs_pure ⟨rfl, by rw [tc, mul_zero, add_zero], fun _ ↦ rfl, fun _ ↦ ⟨rfl, hp⟩, fun h ↦ absurd h (by simp),
      fun _ x hx ↦ ?_, fun h ↦ h⟩
    simp only [if_true, tc]
    simp only [CClaim.val]
    rw [onStackZB_sum _ _ 0 (fun e he ↦ by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact hp e' he') x hx]
    simp only [smallW, List.map_map]
    rfl

end Lvm.QShape
