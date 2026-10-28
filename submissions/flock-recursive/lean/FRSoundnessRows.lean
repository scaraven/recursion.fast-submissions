-- New for `flock-recursive` (BLUEPRINT A.10 rows Lr1–Lr3 and E1–E4, §5.2; stage S-G1j).
import FRSoundnessFront

/-!
# The front's row Spartan unit (Lr, and E once it precedes RS)

A **row Spartan** proves that every row of a list `rows` (`a` row bits, `nc` cell bits) holds on
`f⁽⁰⁾` (`fF`), for the kinds where `on` holds: a zerocheck point (a multi-squeeze phase entered
at `s0`), `a` outer rounds of degree 3 from `b2` (`D3`, claim `0`), an end absorb at
`pe = b2 + 2a` carrying `â, b̂, ĉ` (asserted against the outer claim: `RejEnd`), the batching
squeeze `κ` at `pk = pe + 1`, and `nc` inner rounds of degree 2 from `b4 = pe + 2` (`D2`, its
round checks asserted: `RejIn`). This is E1 … E4 (the M rows, 21 and 23 bits; positions 209,
221, 263, 264, 265 under revision 3.13) and Lr1 … Lr3 (`lRows`, 15 bits; positions 169,
178, 208, 209), whose inner rounds are E4's since revision 3.13 (six claims batched by
`κ_E`). The algebra is S-C's
(`FRSpartan`: `zc_start`, `outer_trueSum`, `outer_final`, `triple_wrong`, `inner_trueSum`,
`batch_escape_le`, `inner_final`).

The unit's doom parts, phase by phase: **`RowsBad`** (some row fails; before the zerocheck),
**`ZCw`** (the residual's extension at the zerocheck point is nonzero; the zerocheck's final
doom), **`D3`** (the outer rounds), **`EndBad`** (a wrong triple), **`BatBad`** (a false batched
claim) and **`D2`** (the inner rounds; after the last round it is the claim handed to ring
switching). The obligations, each in the form `FrontObl`'s fields take for a phase doom
`Bg ∨ U` (the background read before the phase, `FRSoundnessFront`):

* **`zc_hfin`** (the zerocheck's charge, `≤ a/2^128`), **`habs_outer`** (into the outer rounds),
  **`habs_end`** (`D3` at the end absorb gives a wrong triple, or `RejEnd`), **`single_batch`**
  (at most `2·2^128` answers at `κ`), **`habs_inner`** (into the inner rounds);
* inside the round phases the existing `D3_append_iff`, `D3_single`, `D2_append_iff`,
  `D2_single` apply to `T3`, `T4` (**`T3_local`**, **`T4_local`**, the sizes);
* **`rejEnd_ok`**/**`rejIn_ok`** (`RejOK`), and the reads (**`rowsBad_reads`**, **`zcw_reads`**,
  **`endBad_reads`**, **`batBad_reads`**).

**Revision 3.13** withdrew Lr4 (its `evalL` point was 15 coordinates, `evalL_short_zero`) and put
E before RS (`e4_before_rs0`); E4's lincheck now batches Lr's three claims with M's (`κ_E³`), so the
unit's inner half is instantiated once, for E4 with the batched claim (S-G's next step; this
module's batching is still the three-claim one). The zerocheck half is instantiated for Lr
(`lr_unit_pos`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

theorem capPos_zero : capPos 0 = 2 := by
  simp only [capPos]; rw [phStart, fsStarts_eq]; rfl

section RowSpartan

variable (rows : List Circ.Row) (a nc : ℕ) (on : Kind → Bool)

/-- The rows' `A`, `B`, `C` (`rowMat`). -/
abbrev mA : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.a rows a nc
abbrev mB : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.b rows a nc
abbrev mC : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.c rows a nc

/-- `f⁽⁰⁾` on the cells. -/
noncomputable def zC (L es : Log) : Fin (2 ^ nc) → F := fun y => fF (kindOf es) L es y

/-- **The unit's statement fails**: for a kind it runs on, `f⁽⁰⁾` violates the rows' R1CS. -/
def RowsBad (L es : Log) : Prop :=
  on (kindOf es) = true ∧ ¬ Sat (mA rows a nc) (mB rows a nc) (mC rows a nc) (zC nc L es)

variable (s0 b2 : ℕ)

/-- The zerocheck point: the phase's first `a` F coordinates. -/
def tauS (es : Log) : List F := (List.range a).map (coordAt es s0)

/-- **The zerocheck's final doom**: the residual's extension at the point is nonzero. -/
noncomputable def ZCw (L es : Log) : Prop :=
  on (kindOf es) = true ∧
    mle (residual (mA rows a nc) (mB rows a nc) (mC rows a nc) (zC nc L es))
      (ptOf a (tauS a s0 es)) ≠ 0

/-- The outer rounds' real count. -/
def nr3 (κ : Kind) : ℕ := if on κ then a else 0

/-- The outer tables `eq(τ, ·)`, `Az`, `Bz`, `Cz` (none for the kinds it does not run on). -/
noncomputable def T3 (L es : Log) : Array (Array F) :=
  if on (kindOf es) then outerTables (tauS a s0 es) (mA rows a nc) (mB rows a nc) (mC rows a nc)
    (zC nc L es) else #[]

/-- The outer rounds' challenges. -/
def rxs (es : Log) : List F := rchs b2 es a

/-- The end absorb's three values `â, b̂, ĉ`. -/
def vEnd (es : Log) (j : ℕ) : F := readF (msgAt es (b2 + 2 * a)) (16 * j)

/-- The true triple at the outer rounds' point. -/
noncomputable def triT (L es : Log) : F × F × F :=
  (mle (matVec (mA rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (mB rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (mC rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)))

/-- **A wrong triple** after the end absorb. -/
noncomputable def EndBad (L es : Log) : Prop :=
  on (kindOf es) = true ∧ b2 + 2 * a < es.length ∧
    (vEnd a b2 es 0, vEnd a b2 es 1, vEnd a b2 es 2) ≠ triT rows a nc b2 L es

/-- **The end check** (`finLr` (ii), `finE` (ii)) fails: the outer claim is not
`eq(τ, r)·(â b̂ + ĉ)`. -/
def RejEnd (L es : Log) : Prop :=
  on (kindOf es) = true ∧ b2 + 2 * a < es.length ∧
    clR b2 (fun _ _ => 0) L es a ≠ eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
      (vEnd a b2 es 0 * vEnd a b2 es 1 + vEnd a b2 es 2)

/-- The batching challenge `κ` (at `pk = b2 + 2a + 1`). -/
def kapB (es : Log) : F := fAt es (b2 + 2 * a + 1) 0

/-- The batched claim `â + κ b̂ + κ² ĉ` (`finLr` (iii), `finE` (iii)): the inner rounds' start. -/
def c4 (_L es : Log) : F :=
  vEnd a b2 es 0 + kapB a b2 es * vEnd a b2 es 1 + kapB a b2 es ^ 2 * vEnd a b2 es 2

/-- The inner rounds' real count. -/
def nr4 (κ : Kind) : ℕ := if on κ then nc else 0

/-- The inner tables `M̃_κ(r, ·)` and `z`. -/
noncomputable def T4 (L es : Log) : Array (Array F) :=
  if on (kindOf es) then innerTables (ptOf a (rxs a b2 es)) (kapB a b2 es) (mA rows a nc)
    (mB rows a nc) (mC rows a nc) (zC nc L es) else #[]

/-- **A false batched claim** after `κ`. -/
noncomputable def BatBad (L es : Log) : Prop :=
  on (kindOf es) = true ∧ b2 + 2 * a + 1 < es.length ∧
    c4 a b2 L es ≠ trueSum innerExpr (T4 rows a nc on b2 L es) nc

/-- The inner rounds (F, degree 2, from `b4 = b2 + 2a + 2`). -/
abbrev D4 : Log → Log → Prop :=
  D2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) (nr4 nc on) innerExpr
    (T4 rows a nc on b2)

/-- **The inner rounds' checks** fail: some absorbed round's `g(0) + g(1)` is not its claim. -/
def RejIn (L es : Log) : Prop :=
  ∃ l < nr4 nc on (kindOf es), b2 + 2 * a + 2 + 2 * l < es.length ∧
    ¬ Chk2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) L es l

/-! ### Reads -/

variable {rows a nc on s0 b2}

theorem zC_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp : 3 ≤ p) :
    zC nc L es = zC nc L' es' := by
  funext y
  simp only [zC, fF, h.kind (by omega),
    fTab_same h (by norm_num : 0 < 5) (kindOf es') (by rw [capPos_zero]; omega)]

theorem tauS_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : s0 + 1 + (a + 1) / 2 ≤ p) :
    tauS a s0 es = tauS a s0 es' := by
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  simp only [coordAt, fAt, ansAt]
  rw [h (s0 + 1 + j / 2) (by omega)]

theorem rowsBad_reads : Reads 3 (RowsBad rows a nc on) :=
  fun L es L' es' _ _ h => by simp only [RowsBad, h.kind (by norm_num), zC_same h le_rfl]

theorem zcw_reads (hp : 3 ≤ s0 + 1 + (a + 1) / 2) :
    Reads (s0 + 1 + (a + 1) / 2) (ZCw rows a nc on s0) :=
  fun L es L' es' _ _ h => by
    simp only [ZCw, h.kind (by omega), zC_same h hp, tauS_agree h.1 le_rfl]

theorem rxs_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a ≤ p) :
    rxs a b2 es = rxs a b2 es' := by
  unfold rxs; exact rchs_congr (h.mono hp)

theorem vEnd_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 1 ≤ p)
    (j : ℕ) : vEnd a b2 es j = vEnd a b2 es' j := by
  simp only [vEnd, msgAt, h (b2 + 2 * a) (by omega)]

theorem kapB_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 2 ≤ p) :
    kapB a b2 es = kapB a b2 es' := by
  simp only [kapB, fAt, ansAt, h (b2 + 2 * a + 1) (by omega)]

theorem triT_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp3 : 3 ≤ p)
    (hp : b2 + 2 * a ≤ p) : triT rows a nc b2 L es = triT rows a nc b2 L' es' := by
  simp only [triT, zC_same h hp3, rxs_agree h.1 hp]

theorem endBad_reads (h3 : 3 ≤ b2) : Reads (b2 + 2 * a + 1) (EndBad rows a nc on b2) :=
  fun L es L' es' h1 h2 h => by
    have hk := h.kind (by omega)
    simp only [EndBad, hk, triT_same h (by omega) (by omega : b2 + 2 * a ≤ b2 + 2 * a + 1),
      vEnd_agree h.1 le_rfl]
    exact and_congr_right fun _ => ⟨fun h' => ⟨by omega, h'.2⟩, fun h' => ⟨by omega, h'.2⟩⟩

theorem T4_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp3 : 3 ≤ p)
    (hp : b2 + 2 * a + 2 ≤ p) : T4 rows a nc on b2 L es = T4 rows a nc on b2 L' es' := by
  simp only [T4, h.kind (by omega), zC_same h hp3, rxs_agree h.1 (by omega : b2 + 2 * a ≤ p),
    kapB_agree h.1 hp]

theorem c4_agree {L L' es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 2 ≤ p) :
    c4 a b2 L es = c4 a b2 L' es' := by
  simp only [c4, vEnd_agree h (by omega : b2 + 2 * a + 1 ≤ p), kapB_agree h hp]

theorem batBad_reads (h3 : 3 ≤ b2) : Reads (b2 + 2 * a + 2) (BatBad rows a nc on b2) :=
  fun L es L' es' h1 h2 h => by
    have hk := h.kind (by omega)
    simp only [BatBad, hk, T4_same h (by omega) le_rfl, c4_agree (L := L) (L' := L') h.1 le_rfl]
    exact and_congr_right fun _ => ⟨fun h' => ⟨by omega, h'.2⟩, fun h' => ⟨by omega, h'.2⟩⟩

/-- The outer tables read the entries before `b2` (`TruthLocal`). -/
theorem T3_local (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    TruthLocal b2 (fun _ _ => 0) (T3 rows a nc on s0) := fun L es es' h => by
  have hS := same_of_agree L h
  refine ⟨?_, rfl⟩
  simp only [T3, hS.kind (by omega), zC_same hS h3, tauS_agree h hs]

theorem T3_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) : T3 rows a nc on s0 L es = T3 rows a nc on s0 L' es' := by
  simp only [T3, h.kind (by omega), zC_same h hp3, tauS_agree h.1 hs]

/-- The inner tables and claim read the entries before `b4` (`TruthLocal2`). -/
theorem T4_local (h3 : 3 ≤ b2) :
    TruthLocal2 (b2 + 2 * a + 2) (c4 a b2) (T4 rows a nc on b2) := fun L es es' h =>
  ⟨T4_same (same_of_agree L h) (by omega) le_rfl, c4_agree h le_rfl⟩

theorem T3_size (L es : Log) :
    ∀ t ∈ T3 rows a nc on s0 L es, t.size = 2 ^ nr3 a on (kindOf es) := by
  unfold T3 nr3
  split_ifs with h
  · exact outer_sizes _ (by simp [tauS]) _ _ _ _
  · simp

theorem T4_size (L es : Log) :
    ∀ t ∈ T4 rows a nc on b2 L es, t.size = 2 ^ nr4 nc on (kindOf es) := by
  unfold T4 nr4
  split_ifs with h
  · simp [innerTables]
  · simp

/-! ### The zerocheck's charge (`hfin`) -/

theorem tbl0_ne_zero (X : Array F) : tbl 0 X ≠ 0 ↔ tbl 0 X 0 ≠ 0 := by
  constructor
  · intro h h0; apply h; funext u
    rw [show u = 0 from Fin.ext (by have := u.isLt; simp at this; omega), h0]; rfl
  · intro h h0; exact h (by rw [h0]; rfl)

theorem mlDoom_full {n : ℕ} (t : Array F) (ht : t.size = 2 ^ n) (l : List F) (hl : n ≤ l.length) :
    mlDoom n t l ↔ mle (tbl n t) (ptOf n (l.take n)) ≠ 0 := by
  have hlen : (l.take n).length = n := by simp; omega
  have hb := bindL_mle (l.take n) t (by rw [hlen, ht])
  rw [pt_eq_ptOf, hlen] at hb
  unfold mlDoom
  rw [hlen, Nat.sub_self, tbl0_ne_zero, hb]

theorem take_ofFn_coord (es : Log) {r : ℕ} (ha : a ≤ r * 2) :
    (List.ofFn fun j : Fin (r * 2) => coordAt es s0 j).take a = tauS a s0 es := by
  apply List.ext_getElem (by simp [tauS]; omega)
  intro j h1 h2
  simp [tauS]

open Classical in
/-- **The zerocheck's charge** (A.10 Lr1/E1, `ml_round_le`): with the doom of the phase's entry
`Bg ∨ RowsBad` and its final doom `Bg ∨ ZCw`, the phase costs at most `a/2^128 ≤ deltaR`. -/
theorem zc_hfin {Dk : ℕ → Log → Log → Prop} {r : ℕ} (hmem : (s0, r) ∈ fsRanges)
    {Bg : Log → Log → Prop} (hBg : Reads (s0 + 1) Bg) (h3 : 2 ≤ s0) (ha : a ≤ r * 2)
    (ha' : a ≤ 239)
    (hprev : Dk (phOf s0) = fun L es => Bg L es ∨ RowsBad rows a nc on L es)
    (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) (fun L es => Bg L es ∨ ZCw rows a nc on s0 L es)
      s0 r)
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR := by
  set t := Array.ofFn (residual (mA rows a nc) (mB rows a nc) (mC rows a nc) (zC nc L es₀))
  have ht : t.size = 2 ^ a := by simp [t]
  by_cases hd : RowsBad rows a nc on L es₀
  · refine (ml_round_le hl ha ht (zc_start hd.2) fun as has he => ?_).trans (coord_le_deltaR ha')
    obtain ⟨-, -, hnf⟩ := esc_msD_frame hmem hBg hprev hfin hl as has he
    have hS := (same_append L es₀ []).mono (le_refl es₀.length)
    obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
    have hS' : Same L (ext es₀ as) L es₀ (s0 + 1) := by
      rw [hy, ← hl]; exact same_append L es₀ ys
    have hk : kindOf (ext es₀ as) = kindOf es₀ := hS'.kind (by omega)
    have hz : zC nc L (ext es₀ as) = zC nc L es₀ := zC_same hS' (by omega)
    have hlen : a ≤ (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j).length := by
      simp; omega
    rw [mlDoom_full t ht _ hlen, tbl_ofFn]
    intro hm
    apply hnf
    refine ⟨by rw [hk]; exact hd.1, ?_⟩
    rw [hz]
    rwa [take_ofFn_coord (ext es₀ as) ha] at hm
  · rw [condCount_eq_zero fun as has he =>
      hd (esc_msD_frame hmem hBg hprev hfin hl as has he).2.1]
    exact zero_le

/-! ### The handoffs -/

/-- **Into the outer rounds** (`habs` at `b2`): a nonzero residual at the point makes the outer
claim `0` false. -/
theorem habs_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest)
    (hl : es.length = b2) (hz : ZCw rows a nc on s0 L es) :
    D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by omega)
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 b2 (nr3 a on) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]
    rw [show b2 + 1 - b2 = 1 by omega]; simp
  rw [ha0]
  simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  have hT : T3 rows a nc on s0 L (es ++ [x]) = T3 rows a nc on s0 L es :=
    T3_same hS (by omega) (by omega)
  rw [hT, hk]
  simp only [T3, nr3, hz.1, ite_true]
  exact outer_start _ (by simp [tauS]) hz.2

/-- **At the end absorb** (`habs` at `pe = b2 + 2a`): a doomed outer claim with every round
answered gives a wrong triple, or the end check fails. -/
theorem habs_end (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest)
    (hl : es.length = b2 + 2 * a)
    (hd : D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L es) :
    RejEnd a on s0 b2 L (es ++ [x]) ∨ EndBad rows a nc on b2 L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by omega)
  obtain ⟨hlt, hw⟩ := hd
  by_cases hon : on (kindOf es) = true
  swap
  · exfalso
    have : ans3 b2 (nr3 a on) es = 0 := by simp [ans3, nr3, hon]
    rw [this] at hw
    simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, T3, hon, nr3] at hw
    exact hw (by simp [trueSum, tbl, outerExpr, Expr.eval])
  have ha : ans3 b2 (nr3 a on) es = a := by
    simp only [ans3, nr3, hon, ite_true, hl]; rw [show b2 + 2 * a - b2 = 2 * a by omega]; simp
  rw [ha] at hw
  unfold Wrong3 at hw
  have hfin : trueSum outerExpr (bindAll (T3 rows a nc on s0 L es) (rchs b2 es a))
      (nr3 a on (kindOf es) - a) = eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
        ((triT rows a nc b2 L es).1 * (triT rows a nc b2 L es).2.1 +
          (triT rows a nc b2 L es).2.2) := by
    simp only [T3, nr3, hon, ite_true, Nat.sub_self]
    exact outer_final _ _ (by simp [tauS]) (by simp [rchs]) _ _ _ _
  rw [hfin] at hw
  have hag := agree_append es [x] (le_of_eq hl.symm)
  have hc : clR b2 (fun _ _ => 0) L (es ++ [x]) a = clR b2 (fun _ _ => 0) L es a :=
    clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L) (es := es ++ [x]) (es' := es) rfl
      (l := a) (hag.mono (by omega))
  have hτ := tauS_agree (a := a) (s0 := s0) hag (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) hag le_rfl
  by_cases hrej : RejEnd a on s0 b2 L (es ++ [x])
  · exact Or.inl hrej
  right
  refine ⟨by rw [hk]; exact hon, by simp; omega, ?_⟩
  have hchk : clR b2 (fun _ _ => 0) L (es ++ [x]) a =
      eq (ptOf a (tauS a s0 (es ++ [x]))) (ptOf a (rxs a b2 (es ++ [x]))) *
        (vEnd a b2 (es ++ [x]) 0 * vEnd a b2 (es ++ [x]) 1 + vEnd a b2 (es ++ [x]) 2) := by
    by_contra hne; exact hrej ⟨by rw [hk]; exact hon, by simp; omega, hne⟩
  rw [triT_same hS (by omega) (by omega)]
  rw [hc, hτ, hr] at hchk
  intro heq
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  apply hw
  rw [hchk, heq.1, heq.2.1, heq.2.2]

open Classical in
/-- **At the batching squeeze** (`hsingle` at `pk`, A.10 Lr3/E3, `batch_escape_le`): from a wrong
triple, at most `2·2^128` answers make the batched claim true. -/
theorem single_batch (h3 : 3 ≤ b2) (L es : Log) (hl : es.length = b2 + 2 * a + 1) :
    (univ.filter fun d => EndBad rows a nc on b2 L es ∧
      ¬ BatBad rows a nc on b2 L (ext1 es d)).card ≤ 2 * 2 ^ 128 := by
  by_cases hd : EndBad rows a nc on b2 L es
  swap
  · rw [filter_false_of_mem fun d _ h => hd h.1]; simp
  obtain ⟨hon, -, hne⟩ := hd
  have hS : ∀ d, Same L (ext1 es d) L es es.length := fun d => same_append L es _
  set S := univ.filter fun ρ : F => vEnd a b2 es 0 + ρ * vEnd a b2 es 1 + ρ ^ 2 * vEnd a b2 es 2 =
    trueSum innerExpr (innerTables (ptOf a (rxs a b2 es)) ρ (mA rows a nc) (mB rows a nc)
      (mC rows a nc) (zC nc L es)) nc
  have hSc : S.card ≤ 2 := batch_escape_le _ _ _ _ _ (by unfold triT at hne; exact hne)
  refine le_trans (card_le_card (t := univ.filter fun d : Digest => chF d 0 ∈ S)
    fun d hd' => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ hSc)
  simp only [mem_filter, mem_univ, true_and] at hd' ⊢
  obtain ⟨-, hnb⟩ := hd'
  simp only [S, mem_filter, mem_univ, true_and]
  have hk : kindOf (ext1 es d) = kindOf es := (hS d).kind (by omega)
  have hag : Agree (ext1 es d) es es.length := agree_append es _ le_rfl
  have hκ : kapB a b2 (ext1 es d) = chF d 0 := by
    simp only [kapB, fAt, ansAt, ← hl]
    exact congrArg (chF · 0) (entAt_ext1 es d)
  by_contra hc
  apply hnb
  refine ⟨by rw [hk]; exact hon, by simp [ext1]; omega, ?_⟩
  have hr := rxs_agree (a := a) (b2 := b2) hag (by omega)
  have hv := fun j => vEnd_agree (a := a) (b2 := b2) hag (by omega) j
  have hz := zC_same (nc := nc) (hS d) (by omega)
  unfold c4 T4
  rw [hk, ite_pos' hon, hκ, hz, hr, hv 0, hv 1, hv 2]
  exact hc

/-- **Into the inner rounds** (`habs` at `b4`): a false batched claim is the inner rounds' doom. -/
theorem habs_inner (h3 : 3 ≤ b2) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = b2 + 2 * a + 2) (hb : BatBad rows a nc on b2 L es) :
    D4 rows a nc on b2 L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by omega)
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 (b2 + 2 * a + 2) (nr4 nc on) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]
    rw [show b2 + 2 * a + 2 + 1 - (b2 + 2 * a + 2) = 1 by omega]; simp
  rw [ha0]
  simp only [Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [T4_same hS (by omega) (by omega), hk, c4_agree (L := L) (L' := L) hS.1 (by omega)]
  have := hb.2.2
  simp only [nr4, hb.1, ite_true]
  exact this

/-! ### `RejOK` for the end check and the inner rounds' checks -/

theorem rejEnd_reads (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    Reads (b2 + 2 * a + 1) (RejEnd a on s0 b2) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  have hc : clR b2 (fun _ _ => (0 : F)) L es a = clR b2 (fun _ _ => 0) L' es' a :=
    (clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl a).trans
      (clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
        (l := a) (h.1.mono (by omega)))
  have hτ := tauS_agree (a := a) (s0 := s0) h.1 (by omega)
  have hr := rxs_agree (a := a) (b2 := b2) h.1 (by omega)
  have hv := fun j => vEnd_agree (a := a) (b2 := b2) h.1 le_rfl j
  unfold RejEnd
  rw [hk, hc, hτ, hr, hv 0, hv 1, hv 2]
  exact and_congr_right fun _ => ⟨fun h' => ⟨by omega, h'.2⟩, fun h' => ⟨by omega, h'.2⟩⟩

theorem rejEnd_ok (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2)
    (hpe : fsItems[b2 + 2 * a]? ≠ some .squeeze) : RejOK (RejEnd a on s0 b2) where
  mono L es x h := by
    have hle : b2 + 2 * a + 1 ≤ es.length := h.2.1
    exact ((rejEnd_reads hs h3).append L es [x] hle).mpr h
  sq L es x hit := by
    by_cases hle : b2 + 2 * a + 1 ≤ es.length
    · exact (rejEnd_reads hs h3).append L es [x] hle
    · constructor
      · intro h
        have h1 := h.2.1
        simp only [List.length_append, List.length_singleton] at h1
        rw [show es.length = b2 + 2 * a by omega] at hit
        exact absurd hit hpe
      · intro h; exact absurd h.2.1 (by omega)
  stab L i hb hci X hX := by
    by_cases hle : b2 + 2 * a + 1 ≤ X.length
    · exact (rejEnd_reads hs h3).stab hb hci hX hle
    · exact ⟨fun h => absurd h.2.1 (by omega), fun h => absurd h.2.1 (by omega)⟩

/-! ### Inside the round phases -/

open Classical in
/-- **An outer round's squeeze** (A.10 Lr2/E2, `D3_single`): at most `3·2^128` answers escape. -/
theorem single_outer (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) (L es : Log) :
    (univ.filter fun d => D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L es ∧
      ¬ D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L (ext1 es d)).card ≤
      3 * 2 ^ 128 :=
  D3_single (by omega) (T3_local hs h3) outerExpr_deg (T3_size) L es

/-- An outer round's absorb (or a dummy round's items) keeps the outer doom. -/
theorem outer_append (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) {L es : Log}
    (x : ByteArray × Digest) (hlen : b2 < es.length)
    (hc : (es.length - b2) % 2 = 0 ∨ nr3 a on (kindOf es) ≤ (es.length - b2) / 2) :
    D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L (es ++ [x]) ↔
      D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L es :=
  D3_append_iff (by omega) (T3_local hs h3) x hlen hc

open Classical in
/-- **An inner round's squeeze** (A.10 E4, `D2_single` with `card_chF_fiber`): with the
round's check holding, at most `2·2^128` answers escape. -/
theorem single_inner (h3 : 3 ≤ b2) (L es : Log)
    (hchk : ∀ j, es.length = b2 + 2 * a + 2 + 2 * j + 1 → j < nr4 nc on (kindOf es) →
      Chk2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) L es j) :
    (univ.filter fun d => D4 rows a nc on b2 L es ∧ ¬ D4 rows a nc on b2 L (ext1 es d)).card ≤
      2 * 2 ^ 128 :=
  D2_single (by omega) (T4_local h3) innerExpr_deg card_chF_fiber T4_size L es hchk

/-- An inner round's absorb keeps the inner doom. -/
theorem inner_append (h3 : 3 ≤ b2) {L es : Log} (x : ByteArray × Digest)
    (hlen : b2 + 2 * a + 2 < es.length)
    (hc : (es.length - (b2 + 2 * a + 2)) % 2 = 0 ∨
      nr4 nc on (kindOf es) ≤ (es.length - (b2 + 2 * a + 2)) / 2) :
    D4 rows a nc on b2 L (es ++ [x]) ↔ D4 rows a nc on b2 L es :=
  D2_append_iff (by omega) (T4_local h3) x hlen hc

/-- The inner rounds' checks fail only where `¬ RejIn`'s `Chk2` is asked for: from `¬ RejIn`,
every answered round's check holds (`single_inner`'s hypothesis). -/
theorem chk_of_not_rejIn {L es : Log} (hr : ¬ RejIn a nc on b2 L es) (j : ℕ)
    (hj : es.length = b2 + 2 * a + 2 + 2 * j + 1) (hjn : j < nr4 nc on (kindOf es)) :
    Chk2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

/-! ### Stability of the round dooms -/

/-- The outer doom reads the same off two logs whose words agree (`hstab`, `ChainStab`). -/
theorem D3_same {L L' X : Log} {p : ℕ} (h : Same L X L' X p) (hp3 : 3 ≤ p)
    (hs : s0 + 1 + (a + 1) / 2 ≤ p) :
    D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L X ↔
      D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0) L' X :=
  D3_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (nr := nr3 a on) (e := outerExpr)
    (T3_same h hp3 hs) rfl

/-- The inner doom reads the same off two logs whose words agree. -/
theorem D4_same {L L' X : Log} {p : ℕ} (h : Same L X L' X p) (hp3 : 3 ≤ p)
    (hp : b2 + 2 * a + 2 ≤ p) : D4 rows a nc on b2 L X ↔ D4 rows a nc on b2 L' X :=
  D2_congrL (T4_same h hp3 hp) rfl

/-- **Once every outer round is answered, the outer doom reads before the end absorb** (it is
part of the background of every later phase). -/
theorem D3_reads (hs : s0 + 1 + (a + 1) / 2 ≤ b2) (h3 : 3 ≤ b2) :
    Reads (b2 + 2 * a + 1) (D3 b2 (fun _ _ => 0) (nr3 a on) outerExpr (T3 rows a nc on s0)) :=
  fun L es L' es' h1 h2 h => by
    have hk := h.kind (by omega)
    have hans : ∀ Y : Log, b2 + 2 * a ≤ Y.length →
        ans3 b2 (nr3 a on) Y = nr3 a on (kindOf Y) := fun Y hY => by
      unfold ans3 nr3; split_ifs <;> (simp; try omega)
    unfold D3 Wrong3
    rw [hans es (by omega), hans es' (by omega), hk, T3_same h (by omega) (by omega),
      clR_log_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl,
      clR_congr (b := b2) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
        (h.1.mono (by unfold nr3; split_ifs <;> omega)),
      rchs_congr (h.1.mono (by unfold nr3; split_ifs <;> omega))]
    exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-- **Once every inner round is answered, the inner doom reads before `b4 + 2·nc`**: it is the
claim handed to ring switching (`finLr` (iv), `finE` (iv)). -/
theorem D4_reads (h3 : 3 ≤ b2) : Reads (b2 + 2 * a + 2 + 2 * nc + 1) (D4 rows a nc on b2) :=
  fun L es L' es' h1 h2 h => by
    have hk := h.kind (by omega)
    have hans : ∀ Y : Log, b2 + 2 * a + 2 + 2 * nc ≤ Y.length →
        ans3 (b2 + 2 * a + 2) (nr4 nc on) Y = nr4 nc on (kindOf Y) := fun Y hY => by
      unfold ans3 nr4; split_ifs <;> (simp; try omega)
    unfold D4 D2 Wrong2
    rw [hans es (by omega), hans es' (by omega), hk, T4_same h (by omega) (by omega),
      clR2_same (L' := L') (es' := es') (c4_agree h.1 (by omega))
        (h.1.mono (by unfold nr4; split_ifs <;> omega)),
      rchs2_congr (h.1.mono (by unfold nr4; split_ifs <;> omega))]
    exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-! ### `RejOK` for the inner rounds' checks -/

theorem chk_same {L L' es es' : Log} {p : ℕ} (h : Same L es L' es' p) {j : ℕ}
    (hj : b2 + 2 * a + 2 + 2 * j < p) :
    Chk2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) L es j ↔
      Chk2 (b2 + 2 * a + 2) 16 readF (fun d => chF d 0) (c4 a b2) L' es' j := by
  have hg : g2At (b2 + 2 * a + 2) 16 readF es j = g2At (b2 + 2 * a + 2) 16 readF es' j := by
    simp only [g2At, msgAt, h.1 (b2 + 2 * a + 2 + 2 * j) hj]
  have hc := clR2_same (b := b2 + 2 * a + 2) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c4_agree (L := L) (L' := L') (h.1.mono (by omega)) (le_refl (b2 + 2 * a + 2)))
    (l := j) (h.1.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejIn_same {L L' es es' : Log} {p : ℕ} (h : Same L es L' es' p) (h3 : 3 ≤ b2)
    (hp : es.length ≤ p) (hl : es.length = es'.length) :
    RejIn a nc on b2 L es ↔ RejIn a nc on b2 L' es' := by
  by_cases h0 : es.length = 0
  · constructor <;> rintro ⟨j, -, hlt, -⟩ <;> omega
  have hk := h.kind (by omega)
  unfold RejIn
  rw [hk, hl]
  exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj =>
    not_congr (chk_same h (by omega))

theorem nr4_le (κ : Kind) : nr4 nc on κ ≤ nc := by unfold nr4; split_ifs <;> omega

theorem rejIn_mono {L es : Log} (x : ByteArray × Digest) (h : RejIn a nc on b2 L es) :
    RejIn a nc on b2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  have hS := same_append L es [x]
  refine ⟨j, by rw [hS.kind (by omega)]; exact hj, by simp; omega, fun h' => hc ?_⟩
  exact (chk_same hS (by omega)).mp h'

/-- **`RejOK` for the inner rounds' checks**, given that their round messages are absorbs. -/
theorem rejIn_ok (h3 : 3 ≤ b2)
    (habs4 : ∀ j < nc, fsItems[b2 + 2 * a + 2 + 2 * j]? ≠ some .squeeze) :
    RejOK (RejIn a nc on b2) where
  mono L es x := rejIn_mono x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejIn_mono x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    have hS := same_append L es [x]
    have hk := hS.kind (by omega)
    rw [hk] at hj
    by_cases he : b2 + 2 * a + 2 + 2 * j = es.length
    · exact absurd (he ▸ hit) (habs4 j (lt_of_lt_of_le hj (nr4_le _)))
    exact ⟨j, hj, by omega, fun h' => hc ((chk_same hS (by omega)).mpr h')⟩
  stab L i hb hci X hX := rejIn_same (same_stabX hb hci hX) h3 le_rfl rfl

end RowSpartan

/-! ## Lr's zerocheck half (positions 169 … 209) -/

/-- Lr runs on nodes. -/
def lrOn (κ : Kind) : Bool := κ.isNode

/-- **Lr's positions** (A.4, revision 3.13): the zerocheck point after 169 (8 squeezes, phase 13),
the outer rounds from 178 (phase 14), the end absorb at 208 (phase 15, 48 bytes), `κ_L` at 209
(phase 16, a single squeeze); then E1's first squeeze at 210 (phase 17: Lr4 is withdrawn). -/
theorem lr_unit_pos :
    (169, 8) ∈ fsRanges ∧ phOf 169 = 12 ∧ phOf 170 = 13 ∧ phOf 177 = 13 ∧ phOf 178 = 14 ∧
    phOf 207 = 14 ∧ phOf 208 = 15 ∧ phOf 209 = 16 ∧ phOf 210 = 17 ∧
    fsItems[208]? = some (.absorb 48) ∧ fsItems[209]? = some .squeeze ∧ fsRnd 209 = none ∧
    fsItems[210]? = some .squeeze := by
  refine ⟨by rw [fsRanges_eq]; simp, ?_⟩
  have hph : ∀ q, phOf q = (fsStarts.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel⟩
  unfold fsRnd; rw [fsRanges_eq]; decide

theorem lr_outer_phase : RoundsPhase 178 15 (nr3 15 lrOn) := lr2_phase

open Classical in
/-- **Lr1's charge** (A.10 Lr1: `15/2^128 ≤ deltaR`) for any phase doom `Bg ∨ RowsBad` entering
the zerocheck and `Bg ∨ ZCw` leaving it. -/
theorem lr_zc_hfin {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop} (hBg : Reads 170 Bg)
    (hprev : Dk (phOf 169) = fun L es => Bg L es ∨ RowsBad Layout.lRows 15 23 lrOn L es)
    (hfin : Dk (phOf 170) =
      msD (Dk (phOf 169)) (fun L es => Bg L es ∨ ZCw Layout.lRows 15 23 lrOn 169 L es) 169 8)
    (L es₀ : Log) (hl : es₀.length = 170) : condCount (DPos (Dp Dk)) L es₀ 8 [] ≤ deltaR :=
  zc_hfin lr_unit_pos.1 hBg (by norm_num) (by norm_num) (by norm_num) hprev hfin L es₀ hl

open Classical in
/-- **Lr3's count** (A.10 Lr3: `κ_L`, at most `2·2^128` answers). -/
theorem lr_single_batch (L es : Log) (hl : es.length = 209) :
    (univ.filter fun d => EndBad Layout.lRows 15 23 lrOn 178 L es ∧
      ¬ BatBad Layout.lRows 15 23 lrOn 178 L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  single_batch (by norm_num) L es hl

theorem lr_rejEnd_ok : RejOK (RejEnd 15 lrOn 169 178) :=
  rejEnd_ok (by norm_num) (by norm_num) (by rw [lr_unit_pos.2.2.2.2.2.2.2.2.2.1]; simp)

/-! ## What `final` gets -/

/-- **A chain not doomed at the unit's start satisfies the rows** (A.10's "what `final` gets";
S-G2's `walk_back` supplies `¬ RowsBad` on an accepted chain). -/
theorem rows_of_not_rowsBad {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool}
    (hf : RowsFit rows a nc) {L es : Log} (hon : on (kindOf es) = true)
    (h : ¬ RowsBad rows a nc on L es) : ∀ r ∈ rows, r.Holds (fF (kindOf es) L es) :=
  (sat_rowMat_iff rows hf _).mp (by by_contra hc; exact h ⟨hon, hc⟩)

/-- **The Lr truth** from Lr's start (`truthLr`, `lRows_fit`). -/
theorem truthLr_of {L es : Log} (hon : (kindOf es).isNode = true)
    (h : ¬ RowsBad Layout.lRows 15 23 lrOn L es) : truthLr (kindOf es) L es :=
  rows_of_not_rowsBad lRows_fit hon h

/-! ## Controls -/

/-- Control (positive): a failing row dooms a kind the unit runs on (`sat_rowMat_iff`). -/
theorem rowsBad_of_row {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} (hf : RowsFit rows a nc)
    {L es : Log} (hon : on (kindOf es) = true) {r : Circ.Row} (hr : r ∈ rows)
    (hn : ¬ r.Holds (fun c => fF (kindOf es) L es c)) : RowsBad rows a nc on L es :=
  ⟨hon, fun h => hn ((sat_rowMat_iff rows hf _).mp h r hr)⟩

/-- Control (negative): a kind the unit does not run on is never doomed by it. -/
theorem not_rowsBad_off {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} {L es : Log}
    (hon : on (kindOf es) = false) : ¬ RowsBad rows a nc on L es := fun h => by
  rw [h.1] at hon; exact Bool.noConfusion hon

/-- Control (negative): before the end absorb no triple is wrong. -/
theorem not_endBad_short {rows : List Circ.Row} {a nc b2 : ℕ} {on : Kind → Bool} {L es : Log}
    (h : es.length ≤ b2 + 2 * a) : ¬ EndBad rows a nc on b2 L es := fun hd => by
  have := hd.2.1; omega

/-- Control (negative): `Reads` is not vacuous: the chain's length is not read before `0`. -/
theorem not_reads_length : ¬ Reads 0 fun _ es => 1 ≤ es.length := by
  intro h
  have := (h [] [default] [] [] (by simp) (by simp)
    ⟨fun _ hp => absurd hp (Nat.not_lt_zero _), fun _ _ _ hc => absurd hc (Nat.not_lt_zero _)⟩).mp
    (by simp)
  simp at this

end FR.Snd
