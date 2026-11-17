-- New for lvm2 MP-B (cap pruning, stage S2GB): Q_link's heap, layer and cap gadgets.
import LvmQLinkSound

/-!
# Q_link's gadgets for cap pruning (S2GB)

At S2GB an opened level of cap `m` (`= height − path`) sends only `2^c` nodes of its tree (`c = 1` at `L0`, the
root `c = 0` at `L1`, `L2`). After the level's paths the trace holds the **heap**: for `k = 2^m − 1` down to `2^c`
one node query (13 lanes: the length, `lhs`, `rhs`, the answer `A[k]`). Slot `k` sits at heap index
`2^m − 1 − k`, so its lanes are `H + 13·(2^m − 1 − k) + {0, 1…4, 5…8, 9…12}` from the heap's first lane `H`.

* **`heapTpl`** (`heapLoop`, one 1-D loop of `2^(m−1)` iterations, the first `2^(m−1) − 2^c` real): iteration `i`
  is slot `k = 2^(m−1) − 1 − i` (heap index `2^(m−1) + i`); its `lhs` lanes equal the answer of slot `2k` (heap
  index `2i + 1`) and its `rhs` lanes the answer of slot `2k + 1` (heap index `2i`), and both children's length
  lanes are 64. Strides: 13 on the parent, 26 on the children.
* **`layerTpl`** (`layerLoop`, per position as `capTpl`): the leaf's length lane is the row length; the path's top
  equals heap-bottom slot `2^(m−1) + (x >> 1)` at half `x & 1`, `x = q >> D` from the `m` cap bits. The slot's
  lanes run *down* the trace as `x >> 1` grows, so the address chain multiplies by `g^{−13·2^(z−1)}` (the constant
  `g^{2^64 − 1 − 13·2^(z−1)}`; `g^{2^64−1} = 1` in `K`) for bit `z ≥ 1`, and by `g^4` for bit `0` (the half).
* **`capChkTpl`** (`capChk`, one iteration): for `i < 2^c` the answer of slot `2^c + i` equals cap node `i`'s lanes
  in the FS query that absorbed the cap, and that slot's length lane is 64 (these slots are no heap child).
Uncovered heap-bottom halves are free (π's tail bytes).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

/-- The order of `K`'s multiplicative group: `g^ordK = 1`. -/
abbrev ordK : Nat := 2 ^ 64 - 1

/-- A gated equality `x = y`: `d = x + y`, `gate·d = 0` (rows `t`, `t + 1`). -/
def eqRows (t : Nat) (x y g : Opd) : List LRow :=
  [⟨.lin 1 0, .K, [x, y]⟩, ⟨.assert0, .K, [.cur t, g]⟩]

/-- A gated length check `x = 64` (rows `t`, `t + 1`). -/
def lenRows (t : Nat) (x g : Opd) : List LRow :=
  [⟨.lin 0 (kOf 64), .K, [x, x]⟩, ⟨.assert0, .K, [.cur t, g]⟩]

/-- **The heap template** (20 rows): from the parent's first lane `P` (stride `sp`) and the children's first lane
`C` (heap index `2i`, stride `sc`): `P + 1 + l = C + 13 + 9 + l` (left child `2k`), `P + 5 + l = C + 9 + l` (right
child `2k + 1`), `C = 64`, `C + 13 = 64`; gate `z` (stride `sz`). -/
def heapTpl (P C : Nat) (sp sc : List Nat) (z : Nat) (sz : List Nat) : List LRow :=
  let g : Opd := .abs ⟨.K, z, sz⟩
  let ck (j : Nat) : Opd := .abs ⟨.K, C + j, sc⟩
  let pk (j : Nat) : Opd := .abs ⟨.K, P + j, sp⟩
  ((List.range 4).flatMap fun l => eqRows (2 * l) (pk (1 + l)) (ck (13 + 9 + l)) g) ++
  ((List.range 4).flatMap fun l => eqRows (8 + 2 * l) (pk (5 + l)) (ck (9 + l)) g) ++
  lenRows 16 (ck 0) g ++ lenRows 18 (ck 13) g

/-- **The heap loop** of a level of cap `m` whose heap starts at cell `H`: `2^(m−1)` iterations at strides 13 (parent)
and 26 (children), gated by `z` (stride 1). -/
def heapLoop (m H z : Nat) : BM Unit := do
  let _ ← loop [m - 1] (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1])
  pure ()

/-- The layer address chain's rows for bits `1 … c − 1`: per bit `y + 1` (rows `2y + 2`, `2y + 3`)
`u = (G + 1)·acc`, `acc' = β·u + acc` with `G = g^{ordK − 13·2^y}` (one slot down the trace per step of `x >> 1`). -/
def layerChain (bt : Nat) (sb : List Nat) (c : Nat) : List LRow :=
  (List.range (c - 1)).flatMap fun y =>
    [⟨.lin (gpow (ordK - 13 * 2 ^ y)) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩,
     ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]

/-- **The layer template** (per position; `capTpl`'s shape, `2c + 16` rows): the leaf's length lane is the row length;
the address `α = g^{lo + 4β₀ − 13·Σ_{z≥1} β_z 2^(z−1)}` (row `2c`, `lo` the `lhs` of heap-bottom slot `2^(c−1)`, i.e.
`x >> 1 = 0`), `g^l·α`, four `readd`s, and the four answer lanes `A + l` equal to them. -/
def layerTpl (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat) (sz : List Nat) :
    List LRow :=
  let g : Opd := .abs ⟨.K, z, sz⟩
  let e := 2 * c
  [⟨.lin 0 (kOf row), .K, [.abs ⟨.K, lenL, s⟩, .abs ⟨.K, lenL, s⟩]⟩, ⟨.assert0, .K, [.cur 0, g]⟩,
   ⟨.lin (gpow lo * (gpow 4 + 1) + 1) (gpow lo), .K, [.abs ⟨.K, bt, sb⟩, .abs ⟨.K, bt, sb⟩]⟩] ++
  layerChain bt sb c ++
  [⟨.lin (gpow 1 + 1) 0, .K, [.cur e, .cur e]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.lin (gpow 3 + 1) 0, .K, [.cur e, .cur e]⟩,
   ⟨.readd rlo m, .K, [.cur e]⟩, ⟨.readd rlo m, .K, [.cur (e + 1)]⟩, ⟨.readd rlo m, .K, [.cur (e + 2)]⟩,
   ⟨.readd rlo m, .K, [.cur (e + 3)]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 8), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 10), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 12), g]⟩,
   ⟨.lin 1 0, .K, [.cur (e + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (e + 14), g]⟩]

def layerLoop (dims : List Nat) (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) : BM Unit := do
  let _ ← loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz)
  pure ()

/-- The first `lhs` cell of heap-bottom slot `2^(m−1)` (`x >> 1 = 0`): heap index `2^(m−1) − 1`. -/
def layerLo (H m : Nat) : Nat := H + 13 * (2 ^ (m - 1) - 1) + 1

/-- **The cap check template** (one iteration, `10·2^c` rows): for `i < 2^c`, slot `2^c + i` (heap index
`2^m − 1 − 2^c − i`) has length 64 and answer lanes equal to cap node `i`'s (`cap + 4i + l`). -/
def capChkTpl (H m c cap g : Nat) : List LRow :=
  let gt : Opd := .abs ⟨.K, g, []⟩
  (List.range (2 ^ c)).flatMap fun i =>
    let q := H + 13 * (2 ^ m - 1 - 2 ^ c - i)
    lenRows (10 * i) (.abs ⟨.K, q, []⟩) gt ++
    (List.range 4).flatMap fun l =>
      eqRows (10 * i + 2 + 2 * l) (.abs ⟨.K, q + 9 + l, []⟩) (.abs ⟨.K, cap + 4 * i + l, []⟩) gt

def capChk (H m c cap g : Nat) : BM Unit := do
  let _ ← loop [] (capChkTpl H m c cap g)
  pure ()

/-! ## Specifications (CAP-FRZ C, statement first) -/

/-- **Lane `j` of heap slot `k`** of a level of cap `m` whose heap starts at cell `H`: slot `k` is heap entry
`2^m − 1 − k` (13 lanes: `0` the length, `1…4` `lhs`, `5…8` `rhs`, `9…12` the answer). -/
def hcell (H m k j : Nat) : Nat := H + 13 * (2 ^ m - 1 - k) + j

/-- **`g` has order dividing `2^64 − 1`** (`K = GF(2^64)`): the layer chain's constants `g^{ordK − a}` are `g^{−a}`. -/
theorem gpow_ordK : gpow ordK = 1 := by
  letI : Fintype FK := Fintype.ofFinite FK
  have hx : FK.x ≠ 0 := by decide
  have h := FiniteField.pow_card_sub_one_eq_one FK.x hx
  rw [Lvm.FK.card_FK] at h
  exact h

/-! Proof help: gated equality and length rows. -/

theorem gEq_of {c : Ctx} {M : Mem} {o : LoopOut} {jf t : Nat} (hjf : jf < 2 ^ o.dims.sum) {x y g : Opd}
    (h1 : o.tpl.getD t default = ⟨.lin 1 0, .K, [x, y]⟩) (h2 : o.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, g]⟩)
    (hR : LRel c M o jf t) (hS : LAssert M o jf (t + 1)) (hg : g.val M o jf = FE.ofK 1) {X Y : FK}
    (hx : x.val M o jf = FE.ofK X) (hy : y.val M o jf = FE.ofK Y) : X = Y := by
  have hl := lrel_lin h1 hR
  have ha := lassert_of h2 hS
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ha
  rw [Opd.val_cur _ _ hjf, hl, hx, hy, hg, ofK_one, one_mul, ofK_zero, add_zero, one_mul, ← ofK_add] at ha
  exact char2_eq (ofK_inj (ha.trans ofK_zero.symm))

theorem gLen_of {c : Ctx} {M : Mem} {o : LoopOut} {jf t : Nat} (hjf : jf < 2 ^ o.dims.sum) {x g : Opd} {v : FK}
    (h1 : o.tpl.getD t default = ⟨.lin 0 v, .K, [x, x]⟩) (h2 : o.tpl.getD (t + 1) default = ⟨.assert0, .K, [.cur t, g]⟩)
    (hR : LRel c M o jf t) (hS : LAssert M o jf (t + 1)) (hg : g.val M o jf = FE.ofK 1) {X : FK}
    (hx : x.val M o jf = FE.ofK X) : X = v := by
  have hl := lrel_lin h1 hR
  have ha := lassert_of h2 hS
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ha
  rw [Opd.val_cur _ _ hjf, hl, hx, hg, ofK_one, one_mul, ofK_zero, zero_mul, add_zero, ← ofK_add] at ha
  exact char2_eq (ofK_inj (ha.trans ofK_zero.symm))

theorem flatMap_range_getD {α : Type} (f : Nat → List α) (w : Nat) (hf : ∀ i, (f i).length = w) (d : α) :
    ∀ n i r, i < n → r < w → ((List.range n).flatMap f).getD (w * i + r) d = (f i).getD r d
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, r, hi, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen : ((List.range n).flatMap f).length = w * n := by
      rw [List.length_flatMap]; simp [hf, Nat.mul_comm]
    rcases Nat.lt_or_ge i n with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith), flatMap_range_getD f w hf d n i r h hr]
    · obtain rfl : i = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

/-- **The heap check** (`heapLoop`): with the gate `1` at slot `k`'s iteration (`i = 2^(m−1) − 1 − k`), slot `k`'s
`lhs` lanes are the answer of slot `2k`, its `rhs` lanes the answer of slot `2k + 1`, and both children's length lanes
are 64. -/
theorem heapLoop_spec {cx : Ctx} {M : Mem} {p : Ptr} {m H z : Nat}
    (h : SegsHold cx M p (heapLoop m H z p).2) (hA : SegsAssert M p (heapLoop m H z p).2)
    {k : Nat} (hk : 1 ≤ k) (hkm : k < 2 ^ (m - 1)) (hm : 1 ≤ m) (hz : M.k (z + (2 ^ (m - 1) - 1 - k)) = 1) :
    (∀ l < 4, M.k (hcell H m k (1 + l)) = M.k (hcell H m (2 * k) (9 + l)) ∧
      M.k (hcell H m k (5 + l)) = M.k (hcell H m (2 * k + 1) (9 + l))) ∧
    M.k (hcell H m (2 * k) 0) = kOf 64 ∧ M.k (hcell H m (2 * k + 1) 0) = kOf 64 := by
  simp only [heapLoop, hold_bind, assert_bind] at h hA
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hi : 2 ^ (m - 1) - 1 - k < 2 ^ [m - 1].sum := by simp only [List.sum_cons, List.sum_nil, Nat.add_zero]; omega
  have hlen : (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).length = 20 := by
    simp [heapTpl, eqRows, lenRows]
  have hR := fun t (ht : t < 20) => loop_rel h.1 hi (t := t) (by rw [hlen]; exact ht)
  have hS := fun t (ht : t < 20) => loop_assert hA.1 hi (t := t) (by rw [hlen]; exact ht)
  have hu := unflat_one' hi
  have vK : ∀ (b st : Nat), (Opd.abs ⟨.K, b, [st]⟩).val M
      (loop [m - 1] (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]) p).1 (2 ^ (m - 1) - 1 - k) =
        FE.ofK (M.k (b + st * (2 ^ (m - 1) - 1 - k))) := fun b st => by
    rw [Opd.val_absK]; show FE.ofK (M.k (b + dot [st] (unflat [m - 1] _))) = _; rw [hu]; simp [dot]
  have hg : (Opd.abs ⟨.K, z, [1]⟩).val M
      (loop [m - 1] (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]) p).1 (2 ^ (m - 1) - 1 - k) = FE.ofK 1 := by
    rw [vK, Nat.one_mul, hz]
  have key : ∀ lv < 4,
      (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (2 * lv) default =
        ⟨.lin 1 0, .K, [.abs ⟨.K, H + 13 * 2 ^ (m - 1) + (1 + lv), [13]⟩, .abs ⟨.K, H + (13 + (9 + lv)), [26]⟩]⟩ ∧
      (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (2 * lv + 1) default =
        ⟨.assert0, .K, [.cur (2 * lv), .abs ⟨.K, z, [1]⟩]⟩ ∧
      (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (8 + 2 * lv) default =
        ⟨.lin 1 0, .K, [.abs ⟨.K, H + 13 * 2 ^ (m - 1) + (5 + lv), [13]⟩, .abs ⟨.K, H + (9 + lv), [26]⟩]⟩ ∧
      (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (8 + 2 * lv + 1) default =
        ⟨.assert0, .K, [.cur (8 + 2 * lv), .abs ⟨.K, z, [1]⟩]⟩ := by
    intro lv hlv; interval_cases lv <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have k16 : (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD 16 default =
      ⟨.lin 0 (kOf 64), .K, [.abs ⟨.K, H + 0, [26]⟩, .abs ⟨.K, H + 0, [26]⟩]⟩ := rfl
  have k17 : (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (16 + 1) default =
      ⟨.assert0, .K, [.cur 16, .abs ⟨.K, z, [1]⟩]⟩ := rfl
  have k18 : (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD 18 default =
      ⟨.lin 0 (kOf 64), .K, [.abs ⟨.K, H + 13, [26]⟩, .abs ⟨.K, H + 13, [26]⟩]⟩ := rfl
  have k19 : (heapTpl (H + 13 * 2 ^ (m - 1)) H [13] [26] z [1]).getD (18 + 1) default =
      ⟨.assert0, .K, [.cur 18, .abs ⟨.K, z, [1]⟩]⟩ := rfl
  have hc : ∀ j a, hcell H m k j = H + 13 * 2 ^ (m - 1) + j + 13 * (2 ^ (m - 1) - 1 - k) ∧
      hcell H m (2 * k) (a) = H + (13 + a) + 26 * (2 ^ (m - 1) - 1 - k) ∧
      hcell H m (2 * k + 1) a = H + a + 26 * (2 ^ (m - 1) - 1 - k) := by
    intro j a; simp only [hcell]; refine ⟨?_, ?_, ?_⟩ <;> omega
  refine ⟨fun l hl => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨k1, k2, -, -⟩ := key l hl
    rw [(hc _ 0).1, (hc 0 _).2.1]
    exact gEq_of hi k1 k2 (hR _ (by omega)) (hS _ (by omega)) hg (vK _ _) (vK _ _)
  · obtain ⟨-, -, k3, k4⟩ := key l hl
    rw [(hc _ 0).1, (hc 0 _).2.2]
    exact gEq_of hi k3 k4 (hR _ (by omega)) (hS _ (by omega)) hg (vK _ _) (vK _ _)
  · rw [(hc 0 0).2.1]
    have := gLen_of hi k18 k19 (hR _ (by omega)) (hS _ (by omega)) hg (vK _ _)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  · rw [(hc 0 0).2.2]
    have := gLen_of hi k16 k17 (hR _ (by omega)) (hS _ (by omega)) hg (vK _ _)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-! Proof help for `layerLoop_spec`: the chain rows, the bit number's low bit and halves, `g^{a}·g^{ordK − b}`. -/

theorem layerChain_length (bt : Nat) (sb : List Nat) (c : Nat) : (layerChain bt sb c).length = 2 * (c - 1) := by
  simp [layerChain, List.length_flatMap, Nat.mul_comm]

theorem layerChain_getD (bt : Nat) (sb : List Nat) (c y : Nat) (hy : y + 1 < c) :
    (layerChain bt sb c).getD (2 * y) default =
      ⟨.lin (gpow (ordK - 13 * 2 ^ y)) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ ∧
    (layerChain bt sb c).getD (2 * y + 1) default =
      ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩ := by
  have hf : ∀ i, ((fun y : Nat => [(⟨.lin (gpow (ordK - 13 * 2 ^ y)) 0, .K, [.cur (2 * (y + 1)), .cur (2 * (y + 1))]⟩ :
      LRow), ⟨.muladd, .K, [.abs ⟨.K, bt + (y + 1), sb⟩, .cur (2 * (y + 1) + 1), .cur (2 * (y + 1))]⟩]) i).length = 2 :=
    fun _ => rfl
  have h0 := flatMap_range_getD _ 2 hf default (c - 1) y 0 (by omega) (by omega)
  have h1 := flatMap_range_getD _ 2 hf default (c - 1) y 1 (by omega) (by omega)
  rw [Nat.add_zero] at h0
  exact ⟨h0, h1⟩

theorem layerTpl_chain (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) {i : Nat} (hi : i < 2 * (c - 1)) :
    (layerTpl lenL row A lo rlo m s bt sb c z sz).getD (3 + i) default = (layerChain bt sb c).getD i default := by
  simp only [layerTpl]
  exact getD_app2 (l₁ := [_, _, _]) (by rw [layerChain_length]; exact hi)

theorem bitSum_mod2 (M : Mem) (bt : Nat) (st J : List Nat) :
    ∀ n, bitSum M bt st J (n + 1) % 2 = bitSum M bt st J (0 + 1)
  | 0 => Nat.mod_eq_of_lt (bitSum_lt M bt st J (0 + 1))
  | n + 1 => by
    have ih := bitSum_mod2 M bt st J n
    rw [bitSum_succ (n := n + 1), pow_succ]
    split <;> omega

theorem bitSum_div2 (M : Mem) (bt : Nat) (st J : List Nat) (n : Nat) :
    bitSum M bt st J (n + 1 + 1) / 2 =
      bitSum M bt st J (n + 1) / 2 + (if M.k (bt + (n + 1) + dot st J) = 1 then 2 ^ n else 0) := by
  rw [bitSum_succ (n := n + 1), pow_succ]
  split <;> omega

theorem ordK_eq : ordK = 18446744073709551615 := rfl

theorem gpow_sub_ord (a b : Nat) (hb : b ≤ a) (hb' : b ≤ ordK) : gpow a * gpow (ordK - b) = gpow (a - b) := by
  rw [← gpow_add, show a + (ordK - b) = (a - b) + ordK by omega, gpow_add, gpow_ordK, mul_one]

theorem ord_of_ginj {N : Nat} (hinj : GInj N) : N ≤ ordK := by
  by_contra hc
  have := hinj 0 ordK (by omega) (by omega) ((pow_zero _).trans gpow_ordK.symm)
  rw [ordK_eq] at this
  exact absurd this (by decide)

/-! Pure index arithmetic of `layerLoop_spec` on free variables (small `omega` contexts). -/
private theorem lx_0 {lo B : Nat} (h : B < 2) : lo + 4 * (B % 2) - 13 * (B / 2) = lo + 4 * B := by omega
private theorem lx_t {lo H Q P r1 r2 d1 d2 : Nat} (hlo : lo + 12 = H + 13 * Q) (hr : r1 = r2)
    (hd : d2 = d1 + P) (hlt : d2 < 2 * P) (hQ : 4 * P ≤ 2 * Q) :
    13 * P ≤ lo + 4 * r1 - 13 * d1 ∧ lo + 4 * r1 - 13 * d1 - 13 * P = lo + 4 * r2 - 13 * d2 := by omega
private theorem lx_d {B P : Nat} (h : B < 4 * P) : B / 2 < 2 * P := by omega
private theorem lx_f {lo B1 B2 B0 : Nat} (hm : B1 % 2 = B0) (hm' : B2 % 2 = B0) (hd : B2 / 2 = B1 / 2 + 0) :
    lo + 4 * (B1 % 2) - 13 * (B1 / 2) = lo + 4 * (B2 % 2) - 13 * (B2 / 2) := by omega
private theorem lx_k2 {P Q H N O : Nat} (hQ : 4 * P ≤ 2 * Q) (hH : H + 13 * Q ≤ N) (hN : N ≤ O) : 13 * P ≤ O := by
  omega
private theorem lx_cell {H Q A lo d r l : Nat} (hA : A = 2 * Q) (hlo : lo + 12 = H + 13 * Q) (hd : d < Q) (hr : r < 2) :
    H + 13 * (A - 1 - (Q + d)) + (1 + 4 * r + l) = lo + 4 * r - 13 * d + l := by omega
private theorem lx_dq {x A Q : Nat} (hA : A = 2 * Q) (hx : x < A) : x / 2 < Q := by omega
private theorem lx_four {H Q lo x N : Nat} (hlo : lo + 12 = H + 13 * Q) (hH : H + 13 * Q ≤ N) :
    lo + 4 * (x % 2) - 13 * (x / 2) + 4 ≤ N := by omega

/-- **The layer check** (`layerLoop`, `capLoop_spec`'s twin): with the gate `1`, Boolean cap bits and `GInj`, the leaf's
length lane is the row length and the path top's four answer lanes are half `x % 2` of heap-bottom slot
`2^(c−1) + x / 2`, `x` the `c` cap bits' number (`lo = layerLo H c`). -/
theorem layerLoop_spec {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A H rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (layerLoop dims lenL row A (layerLo H c) rlo m s bt sb c z sz p).2)
    (hA : SegsAssert M p (layerLoop dims lenL row A (layerLo H c) rlo m s bt sb c z sz p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hc : 1 ≤ c) (hz : M.k (z + dot sz (unflat dims jf)) = 1)
    (hb : ∀ y < c, M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1)
    {N : Nat} (hinj : GInj N) (hN : cx.cells .K ≤ N) (hH : H + 13 * 2 ^ (c - 1) ≤ N) :
    M.k (lenL + dot s (unflat dims jf)) = kOf row ∧ ∀ l < 4, M.k (A + l + dot s (unflat dims jf)) =
      M.k (hcell H c (2 ^ (c - 1) + bitSum M bt sb (unflat dims jf) c / 2)
        (1 + 4 * (bitSum M bt sb (unflat dims jf) c % 2) + l)) := by
  simp only [layerLoop, hold_bind, assert_bind] at h hA
  have hNord := ord_of_ginj hinj
  have hc1 : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have hlo : layerLo H c = H + 13 * (2 ^ (c - 1) - 1) + 1 := rfl
  generalize layerLo H c = lo at h hA hlo
  have hlo' : lo + 12 = H + 13 * 2 ^ (c - 1) := by
    rw [hlo]; have h1 := Nat.one_le_two_pow (n := c - 1); generalize 2 ^ (c - 1) = Q at h1 ⊢; omega
  clear hlo
  have hlen : (layerTpl lenL row A lo rlo m s bt sb c z sz).length = 2 * c + 16 := by
    simp [layerTpl, layerChain_length]; omega
  have hR := fun t (ht : t < 2 * c + 16) => loop_rel h.1 hjf (t := t) (by rw [hlen]; exact ht)
  have hS := fun t (ht : t < 2 * c + 16) => loop_assert hA.1 hjf (t := t) (by rw [hlen]; exact ht)
  generalize hJ : unflat dims jf = J at *
  have vK : ∀ (b : Nat) (st : List Nat),
      (Opd.abs ⟨.K, b, st⟩).val M (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (M.k (b + dot st J)) := fun b st => by
    rw [Opd.val_absK]; show _ = FE.ofK (M.k (b + dot st J)); rw [← hJ]; rfl
  have vc : ∀ t, (Opd.cur t).val M (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  have hzero : ∀ t, t + 1 < 2 * c + 16 →
      (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (t + 1) default =
        ⟨.assert0, .K, [.cur t, .abs ⟨.K, z, sz⟩]⟩ →
      ∀ X : FK, ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M = FE.ofK X → X = 0 := by
    intro t ht hr X hX
    have := lassert_of hr (hS (t + 1) ht)
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, hX] at this
    exact gate_one this hz
  refine ⟨?_, ?_⟩
  · have h0 := lrel_lin (t := 0) rfl (hR 0 (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vK, ofK_zero, zero_mul, add_zero] at h0
    rw [← ofK_add] at h0
    exact char2_eq (hzero 0 (by omega) rfl _ h0)
  · -- the rows past the chain
    have hpost : ∀ i, (layerTpl lenL row A lo rlo m s bt sb c z sz).getD (2 * c + 1 + i) default =
        ([⟨.lin (gpow 1 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.lin (gpow 3 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 1)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 2)]⟩,
         ⟨.readd rlo m, .K, [.cur (2 * c + 3)]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 8), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 10), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 12), .abs ⟨.K, z, sz⟩]⟩,
         ⟨.lin 1 0, .K, [.cur (2 * c + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 14), .abs ⟨.K, z, sz⟩]⟩] :
          List LRow).getD i default := by
      intro i
      have e : 2 * c + 1 + i = [(default : LRow), default, default].length + (layerChain bt sb c).length + i := by
        simp [layerChain_length]; omega
      rw [e]; exact getD_app3
    -- the address chain: `g^{lo + 4·β₀ − 13·⌊x_{y+1}/2⌋}` after bit `y`
    have chain : ∀ y < c, ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * y + 2) jf).val M =
        FE.ofK (gpow (lo + 4 * (bitSum M bt sb J (y + 1) % 2) - 13 * (bitSum M bt sb J (y + 1) / 2))) := by
      intro y
      induction y with
      | zero =>
        intro _
        have hb1 := bitSum_lt M bt sb J (0 + 1)
        have h21 : 2 ^ (0 + 1) = 2 := rfl
        rw [lx_0 (lt_of_lt_of_eq hb1 h21)]
        have h2 := lrel_lin (t := 2) rfl (hR 2 (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK] at h2
        rw [h2, ← ofK_mul, ← ofK_add, ← ofK_add]
        congr 1
        rw [bitSum_succ, show bitSum M bt sb J 0 = 0 from rfl, Nat.zero_add, Nat.add_zero]
        rcases hb 0 hc with h0 | h1
        · simp only [Nat.add_zero] at h0; rw [h0]; simp [show (0 : FK) ≠ 1 from by decide, gpow]
        · simp only [Nat.add_zero] at h1
          rw [h1, if_pos rfl, mul_one]
          have e : (1 : FK) + (gpow lo * (gpow 4 + 1) + 1) + gpow lo =
              gpow lo * gpow 4 + ((1 + 1) + (gpow lo + gpow lo)) := by ring
          rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add]
          simp
      | succ y ih =>
        intro hy
        have ihv := ih (by omega)
        obtain ⟨k1, k2⟩ := layerChain_getD bt sb c y hy
        have r1 := layerTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y) (by omega)
        have r2 := layerTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y + 1) (by omega)
        rw [k1] at r1; rw [k2] at r2
        rw [show 3 + 2 * y = 2 * y + 3 by omega] at r1
        rw [show 3 + (2 * y + 1) = 2 * (y + 1) + 2 by omega] at r2
        have e1 := lrel_lin r1 (hR _ (by omega))
        have e2 := lrel_muladd r2 (hR _ (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_zero, add_zero] at e1 e2
        rw [show 2 * (y + 1) = 2 * y + 2 by ring] at e1 e2
        rw [show 2 * y + 2 + 1 = 2 * y + 3 by ring] at e2
        rw [show 2 * (y + 1) + 2 = 2 * y + 2 + 2 by ring, e2, e1, ihv]
        simp only [← ofK_mul, ← ofK_add]
        congr 1
        have hsel := bit_select
          (gpow (lo + 4 * (bitSum M bt sb J (y + 1) % 2) - 13 * (bitSum M bt sb J (y + 1) / 2)))
          (gpow (ordK - 13 * 2 ^ y)) (M.k (bt + (y + 1) + dot sb J)) (hb (y + 1) hy)
        rw [add_zero] at hsel
        rw [hsel]
        have hm := bitSum_mod2 M bt sb J y
        have hm' := bitSum_mod2 M bt sb J (y + 1)
        have hd := bitSum_div2 M bt sb J y
        have hlt := bitSum_lt M bt sb J (y + 1 + 1)
        have hpc : 2 ^ (y + 1 + 1) ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hy2 : 2 ^ (y + 1 + 1) = 4 * 2 ^ y := by ring
        have hQ : 4 * 2 ^ y ≤ 2 * 2 ^ (c - 1) := by rw [← hy2, ← hc1]; exact hpc
        split_ifs at hd ⊢ with hβ
        · obtain ⟨k1, ke⟩ := lx_t hlo' (hm.trans hm'.symm) hd (lx_d (lt_of_lt_of_eq hlt hy2)) hQ
          rw [gpow_sub_ord _ _ k1 (lx_k2 hQ hH hNord)]
          exact congrArg gpow ke
        · rw [mul_one]; exact congrArg gpow (lx_f hm hm' hd)
    have hα0 := chain (c - 1) (by omega)
    rw [show 2 * (c - 1) + 2 = 2 * c by omega, show c - 1 + 1 = c by omega] at hα0
    have hidx := bitSum_lt M bt sb J c
    generalize bitSum M bt sb J c = x at hα0 hidx ⊢
    have hcellE : ∀ l, hcell H c (2 ^ (c - 1) + x / 2) (1 + 4 * (x % 2) + l) =
        lo + 4 * (x % 2) - 13 * (x / 2) + l := by
      intro l; simp only [hcell]; exact lx_cell hc1 hlo' (lx_dq hc1 hidx) (Nat.mod_lt _ (by decide))
    simp only [hcellE]
    have hfour : lo + 4 * (x % 2) - 13 * (x / 2) + 4 ≤ N := lx_four hlo' hH
    generalize lo + 4 * (x % 2) - 13 * (x / 2) = idx at hα0 hfour ⊢
    -- g^l·α
    have sc : ∀ i < 3, ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
        FE.ofK (gpow (idx + (i + 1))) := by
      intro i hi
      have key : ∀ l, (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 1 + i) default =
          ⟨.lin (gpow l + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩ → l = i + 1 →
          ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
            FE.ofK (gpow (idx + (i + 1))) := by
        intro l hr hl
        have e := lrel_lin hr (hR _ (by omega))
        simp only [List.getD_cons_zero, List.getD_cons_succ, vc, hα0, ofK_zero, add_zero] at e
        rw [e, ← ofK_mul, ← ofK_add, ← hl, ← gpow_scale l, add_zero]
      interval_cases i
      · exact key 1 (hpost 0) rfl
      · exact key 2 (hpost 1) rfl
      · exact key 3 (hpost 2) rfl
    have vcur : ∀ i < 4, (Opd.cur (2 * c + i)).val M (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (gpow (idx + i)) := by
      intro i hi
      rw [vc]
      rcases i with _ | i
      · simpa using hα0
      · have := sc i (by omega); rw [show 2 * c + (i + 1) = 2 * c + 1 + i by omega, this]
    -- the reads
    have rd : ∀ i < 4, ((loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 4 + i) jf).val M =
        FE.ofK (M.k (idx + i)) := by
      intro i hi
      have hr : (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 4 + i) default =
          ⟨.readd rlo m, .K, [.cur (2 * c + i)]⟩ := by
        rw [show 2 * c + 4 + i = 2 * c + 1 + (3 + i) by omega]
        interval_cases i
        · exact hpost 3
        · exact hpost 4
        · exact hpost 5
        · exact hpost 6
      exact lreadd_spec hr (hR _ (by omega)) hinj hN (by omega) (by rw [List.getD_cons_zero, vcur i hi]; rfl)
    intro l hl
    have hr1 : (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l) default =
        ⟨.lin 1 0, .K, [.cur (2 * c + 4 + l), .abs ⟨.K, A + l, s⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l = 2 * c + 1 + (7 + 2 * l) by omega]
      interval_cases l
      · exact hpost 7
      · exact hpost 9
      · exact hpost 11
      · exact hpost 13
    have hr2 : (loop dims (layerTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 8 + 2 * l + 1) default =
        ⟨.assert0, .K, [.cur (2 * c + 8 + 2 * l), .abs ⟨.K, z, sz⟩]⟩ := by
      rw [show 2 * c + 8 + 2 * l + 1 = 2 * c + 1 + (8 + 2 * l) by omega]
      interval_cases l
      · exact hpost 8
      · exact hpost 10
      · exact hpost 12
      · exact hpost 14
    have e := lrel_lin hr1 (hR _ (by omega))
    simp only [List.getD_cons_zero, List.getD_cons_succ, vc, vK, rd l hl, ofK_one, one_mul, ofK_zero, add_zero] at e
    rw [← ofK_add] at e
    exact (char2_eq (hzero _ (by omega) hr2 _ e)).symm

/-- **The cap check** (`capChk`): with the flag `1`, for `i < 2^c` slot `2^c + i` has length 64 and its answer lanes
are cap node `i`'s lanes `cap + 4i + l` in the FS query that absorbed the cap. -/
theorem capChk_spec {cx : Ctx} {M : Mem} {p : Ptr} {H m c cap g : Nat}
    (h : SegsHold cx M p (capChk H m c cap g p).2) (hA : SegsAssert M p (capChk H m c cap g p).2)
    (hg : M.k g = 1) (hcm : c < m) :
    ∀ i < 2 ^ c, M.k (hcell H m (2 ^ c + i) 0) = kOf 64 ∧
      ∀ l < 4, M.k (hcell H m (2 ^ c + i) (9 + l)) = M.k (cap + 4 * i + l) := by
  simp only [capChk, hold_bind, assert_bind] at h hA
  intro i hi
  have h0 : 0 < 2 ^ ([] : List Nat).sum := by simp
  have hw : ∀ i, (lenRows (10 * i) (.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i), []⟩) (.abs ⟨.K, g, []⟩) ++
      (List.range 4).flatMap fun l => eqRows (10 * i + 2 + 2 * l) (.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i) + 9 + l, []⟩)
        (.abs ⟨.K, cap + 4 * i + l, []⟩) (.abs ⟨.K, g, []⟩)).length = 10 := fun i => by
    simp [lenRows, eqRows]
  have hrow : ∀ r < 10, (capChkTpl H m c cap g).getD (10 * i + r) default =
      (lenRows (10 * i) (.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i), []⟩) (.abs ⟨.K, g, []⟩) ++
        (List.range 4).flatMap fun l => eqRows (10 * i + 2 + 2 * l)
          (.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i) + 9 + l, []⟩) (.abs ⟨.K, cap + 4 * i + l, []⟩)
          (.abs ⟨.K, g, []⟩)).getD r default :=
    fun r hr => flatMap_range_getD _ 10 hw default (2 ^ c) i r hi hr
  have hlen : (capChkTpl H m c cap g).length = 10 * 2 ^ c := by
    simp only [capChkTpl]; rw [List.length_flatMap]; simp [lenRows, eqRows, Nat.mul_comm]
  have hR := fun t (ht : t < 10 * 2 ^ c) => loop_rel h.1 h0 (t := t) (by rw [hlen]; exact ht)
  have hS := fun t (ht : t < 10 * 2 ^ c) => loop_assert hA.1 h0 (t := t) (by rw [hlen]; exact ht)
  have vK : ∀ b, (Opd.abs ⟨.K, b, []⟩).val M (loop [] (capChkTpl H m c cap g) p).1 0 = FE.ofK (M.k b) := fun b => by
    rw [Opd.val_absK]; simp [dot]
  have hg' : (Opd.abs ⟨.K, g, []⟩).val M (loop [] (capChkTpl H m c cap g) p).1 0 = FE.ofK 1 := by rw [vK, hg]
  have hq : ∀ j, hcell H m (2 ^ c + i) j = H + 13 * (2 ^ m - 1 - 2 ^ c - i) + j := fun j => by
    simp only [hcell]; congr 2; omega
  have hlt : 10 * i + 10 ≤ 10 * 2 ^ c := by omega
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hq]
    have r0 : (capChkTpl H m c cap g).getD (10 * i) default =
        ⟨.lin 0 (kOf 64), .K, [.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i) + 0, []⟩,
          .abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i) + 0, []⟩]⟩ := by
      have := hrow 0 (by omega); rw [Nat.add_zero] at this; rw [this]; rfl
    have r1 : (capChkTpl H m c cap g).getD (10 * i + 1) default = ⟨.assert0, .K, [.cur (10 * i), .abs ⟨.K, g, []⟩]⟩ := by
      rw [hrow 1 (by omega)]; rfl
    exact gLen_of h0 r0 r1 (hR _ (by omega)) (hS _ (by omega)) hg' (vK _)
  · rw [hq]
    have r2 : (capChkTpl H m c cap g).getD (10 * i + 2 + 2 * l) default =
        ⟨.lin 1 0, .K, [.abs ⟨.K, H + 13 * (2 ^ m - 1 - 2 ^ c - i) + 9 + l, []⟩, .abs ⟨.K, cap + 4 * i + l, []⟩]⟩ := by
      rw [show 10 * i + 2 + 2 * l = 10 * i + (2 + 2 * l) by omega, hrow _ (by omega)]
      interval_cases l <;> rfl
    have r3 : (capChkTpl H m c cap g).getD (10 * i + 2 + 2 * l + 1) default =
        ⟨.assert0, .K, [.cur (10 * i + 2 + 2 * l), .abs ⟨.K, g, []⟩]⟩ := by
      rw [show 10 * i + 2 + 2 * l + 1 = 10 * i + (3 + 2 * l) by omega, hrow _ (by omega)]
      interval_cases l <;> rfl
    have := gEq_of h0 r2 r3 (hR _ (by omega)) (hS _ (by omega)) hg' (vK _) (vK _)
    rw [← Nat.add_assoc]; exact this

end Lvm.Loop.Build
