-- New for lvm6 (WP-PHIV6): the `BITS` kind of `Φ_Q`'s class evaluator. NODE3's F2 lays every row of a `BITS` class
-- (`LvmQTypedBits.chunkRows`, `Lvm6NodeBits.rowBlk6`) as one instance of an auxiliary class: `2^β` booleanity rows
-- (bit word `z` at slot `z`, matrices `bo`) and the word row (slot `iw`, matrix `ow`, bit `z` with coefficient
-- `g^z`) over the instance's first `nb ≤ 2^β` words (`BITS`: `nb = 64`; PoW: `nb = 64 − g`). Their template sum has a closed form in `O(β)` products, so the kind
-- costs `O(β + L)` products a class, none an instance; the outputs and cells stay a class (`CTpl`) and externals.
import Lvm6VPhiGK

/-!
# The `BITS` kind

* **`BKB`**: a class geometry (`xb`, `a`, `yb`, `bb`, `n`, `L`) and the bit template's parameters (`β`, `nb`, `bo`,
  `iw`, `ow`, `g`); **`BKB.tpl`** (the template entries), **`BKB.toCTpl`** (the same as a class with only these
  entries), **`BKB.ents`**, **`BKB.okB`** (`toCTpl`'s check, `β ≤ a`, `β ≤ bb`).
* `gpw` (powers by multiplication), **`powPre`**, **`powPre_eq`**: `Σ_{z<e} g^z·eq(r, z)` by the bits of `e`.
* **`BKB.V0`**: the template's sum on the low tables in closed form (`wPreH` for the booleanity rows, `powPre` for the
  word row), **`BKB.V0_eq`**.
* **`BKB.valW`** (`clsCombF` with `V0`, no previous-instance or fixed-word sums), **`BKB.valW_eq`**: the sum of the
  entries' `qv`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- `g^z` by repeated multiplication. -/
def gpw (g : FE2) : ℕ → FE2
  | 0 => 1
  | z + 1 => gpw g z * g

theorem gpw_add (g : FE2) (u : ℕ) : ∀ v, gpw g (u + v) = gpw g u * gpw g v
  | 0 => by simp [gpw]
  | v + 1 => by rw [← Nat.add_assoc, gpw, gpw, gpw_add g u v, mul_assoc]

theorem gpw_sq (g : FE2) : ∀ u, gpw g (2 * u) = gpw (g * g) u
  | 0 => rfl
  | u + 1 => by
    rw [show 2 * (u + 1) = 2 * u + 1 + 1 by ring, gpw, gpw, gpw, gpw_sq g u, mul_assoc]

/-- **A `BITS` kind**: a class geometry and its bit template's parameters. -/
structure BKB where
  xb : ℕ
  a : ℕ
  yb : ℕ
  bb : ℕ
  n : ℕ
  L : ℕ
  β : ℕ
  nb : ℕ
  bo : List ℕ
  iw : ℕ
  ow : ℕ
  g : FE2
  deriving Inhabited

/-- **The bit template**: booleanity entries `(1, o, z, z)` (`o ∈ bo`, `z < nb`) and the word row
`(g^z, ow, iw, z)`. -/
def BKB.tpl (k : BKB) : List Q4 :=
  (k.bo.flatMap fun o => (List.range k.nb).map fun z => ((1 : FE2), o, z, z)) ++
    (List.range k.nb).map fun z => (gpw k.g z, k.ow, k.iw, z)

/-- A cover of singles only. -/
def sglCov (t : List Q4) : RCov := ⟨⟨#[], #[], #[], #[], (t.map fun e => (⟨e.2.1, e.2.2.1, e.1, e.2.2.2⟩ : CSgl)).toArray⟩, #[]⟩

theorem sglCov_ents (t : List Q4) : (sglCov t).ents = t := by
  have h0 : ∀ (β : ℕ) (sl ce : Array ℕ), (default : FBk).ents β sl ce = [] := fun _ _ _ => rfl
  simp [sglCov, RCov.ents, FCov.ents, h0, Function.comp_def]

/-- The kind as a class with only its template's entries. -/
def BKB.toCTpl (k : BKB) : CTpl := ⟨k.xb, k.a, k.yb, k.bb, k.n, k.L, sglCov k.tpl, sglCov [], sglCov []⟩

/-- **Its entries.** -/
def BKB.ents (k : BKB) : List Q4 := k.toCTpl.ents

/-- **Its start-up check.** -/
def BKB.okB (k : BKB) : Bool :=
  k.toCTpl.okB && decide (k.β ≤ k.a) && decide (k.β ≤ k.bb) && decide (k.nb ≤ 2 ^ k.β)

/-- `(Σ_{z<e} g^z·eq(r, z), g^e·eq(r, e))` by the bits of `e` (`wPreH`'s recursion with the factors
`(1 + r_i, g^{2^i}·r_i)`): at most four products a level. -/
def powPre : FE2 → List FE2 → ℕ → FE2 × FE2
  | g, r :: rs, e =>
    let q := powPre (mulE g g) rs (e / 2)
    let h0 := 1 + r
    let h1 := mulE g r
    (mulE (h0 + h1) q.1 + (if e % 2 = 1 then mulE h0 q.2 else 0), mulE (if e % 2 = 1 then h1 else h0) q.2)
  | g, [], e => (if e = 0 then 0 else 1, if e = 0 then 1 else g)

theorem gpw_eqAt (g r0 : FE2) (rs : List FE2) (x : ℕ) : gpw g x * eqAtF (r0 :: rs) x =
    (if x % 2 = 1 then g * r0 else 1 + r0) * (gpw (g * g) (x / 2) * eqAtF rs (x / 2)) := by
  rw [eqAtF_succ]
  obtain ⟨q, rfl | rfl⟩ : ∃ q, x = 2 * q ∨ x = 2 * q + 1 := ⟨x / 2, by omega⟩
  · rw [if_neg (by omega), if_neg (by omega), show 2 * q / 2 = q by omega, gpw_sq]
    ring
  · rw [if_pos (by omega), if_pos (by omega), show (2 * q + 1) / 2 = q by omega, gpw, gpw_sq]
    ring

theorem powPre_eq : ∀ (r : List FE2) (g : FE2) (e : ℕ), e ≤ 2 ^ r.length →
    powPre g r e = (((List.range e).map fun z => gpw g z * eqAtF r z).sum, gpw g e * eqAtF r e)
  | [], g, e, he => by
    have : e = 0 ∨ e = 1 := by simp at he; omega
    rcases this with rfl | rfl <;> simp [powPre, gpw]
  | r0 :: rs, g, e, he => by
    have hq : e / 2 ≤ 2 ^ rs.length := by simp only [List.length_cons, pow_succ] at he; omega
    rw [powPre, powPre_eq rs (mulE g g) (e / 2) hq]
    simp only [mulE_eq]
    rw [show (fun z => gpw g z * eqAtF (r0 :: rs) z) =
      (fun x => (if x % 2 = 1 then g * r0 else 1 + r0) * (gpw (g * g) (x / 2) * eqAtF rs (x / 2))) from
        funext (gpw_eqAt g r0 rs), gpw_eqAt g r0 rs e]
    have hS := fun q => sum_range_pairG (fun u => gpw (g * g) u * eqAtF rs u) (1 + r0) (r0 * g) q
    obtain ⟨q, rfl | rfl⟩ : ∃ q, e = 2 * q ∨ e = 2 * q + 1 := ⟨e / 2, by omega⟩
    · have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      have h := hS q
      simp only [mul_comm r0 g] at h
      rw [h]
      simp only [e1, e2, show (0 : ℕ) ≠ 1 from by decide, if_false, add_zero]
    · have e3 : (2 * q + 1) % 2 = 1 := by omega
      have e4 : (2 * q + 1) / 2 = q := by omega
      have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      have h := hS q
      simp only [mul_comm r0 g] at h
      rw [range_add1 (2 * q), List.map_append, List.sum_append, h]
      simp only [e1, e2, e3, e4, if_true, show (0 : ℕ) ≠ 1 from by decide, if_false, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]

/-- **The template's sum on the low tables, closed form**: `p`, `r` the slot and word low coordinates. -/
def BKB.V0 (k : BKB) (fa : ℕ → FE2) (p r : List FE2) : FE2 :=
  let zr := eqAtF (r.drop k.β) 0
  let B := mulE (mulE (eqAtF (p.drop k.β) 0) zr) (wPreH (hzip (p.take k.β) (r.take k.β)) k.nb).1
  let W := mulE zr (powPre k.g (r.take k.β) k.nb).1
  mulE (k.bo.foldl (fun s o => s + fa o) 0) B + mulE (mulE (fa k.ow) (eqAtF p k.iw)) W

theorem BKB.V0_eq (k : BKB) (fa : ℕ → FE2) (p r : List FE2) (hp : k.β ≤ p.length) (hr : k.β ≤ r.length)
    (hnb : k.nb ≤ 2 ^ k.β) :
    k.V0 fa p r = (k.tpl.map (qv fa (eqAtF p) (eqAtF r))).sum := by
  have hpt : (p.take k.β).length = k.β := by simp; omega
  have hrt : (r.take k.β).length = k.β := by simp; omega
  have hsp : ∀ z, z < 2 ^ k.β → eqAtF p z = eqAtF (p.take k.β) z * eqAtF (p.drop k.β) 0 := fun z hz => by
    rw [← eq_split p k.β z 0 hp hz, mul_zero, add_zero]
  have hsr : ∀ z, z < 2 ^ k.β → eqAtF r z = eqAtF (r.take k.β) z * eqAtF (r.drop k.β) 0 := fun z hz => by
    rw [← eq_split r k.β z 0 hr hz, mul_zero, add_zero]
  have hB : (wPreH (hzip (p.take k.β) (r.take k.β)) k.nb).1 =
      ((List.range k.nb).map fun z => eqAtF (p.take k.β) z * eqAtF (r.take k.β) z).sum := by
    rw [wPreH_eq, wPre_eq _ _ _ (by rw [hpt, hrt]) (by rw [hpt]; exact hnb)]
  have hW : (powPre k.g (r.take k.β) k.nb).1 =
      ((List.range k.nb).map fun z => gpw k.g z * eqAtF (r.take k.β) z).sum := by
    rw [powPre_eq _ _ _ (by rw [hrt]; exact hnb)]
  unfold BKB.V0 BKB.tpl
  simp only [mulE_eq]
  rw [hB, hW, foldl_add_eq, zero_add, List.map_append, List.sum_append, sum_map_flatMap, List.map_map]
  congr 1
  · rw [← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun o _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun z hz => ?_)
    have hz' := lt_of_lt_of_le (List.mem_range.mp hz) hnb
    simp only [Function.comp_apply, qv]
    rw [hsp z hz', hsr z hz']
    ring
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun z hz => ?_)
    simp only [Function.comp_apply, qv]
    rw [hsr z (lt_of_lt_of_le (List.mem_range.mp hz) hnb)]
    ring

/-- The slot and word blocks' high weights (`CTpl.XH`, `CTpl.YH` of `toCTpl`, without building its template). -/
def BKB.XH (k : BKB) (m : List FE2) : FE2 := eqAtF ((m.drop k.a).drop k.L) (k.xb / 2 ^ (k.a + k.L))
def BKB.YH (k : BKB) (b : List FE2) : FE2 := eqAtF ((b.drop k.bb).drop k.L) (k.yb / 2 ^ (k.bb + k.L))

/-- **The kind's value** (`fa` the matrices' weights, `m`, `b` the slot and word points). -/
def BKB.valW (k : BKB) (fa : ℕ → FE2) (m b : List FE2) : FE2 :=
  clsCombF k.n ((m.drop k.a).take k.L) ((b.drop k.bb).take k.L) (k.XH m) (k.YH b)
    (k.V0 fa (m.take k.a) (b.take k.bb)) 0 0

/-- **The `BITS` kind is the sum of its entries.** -/
theorem BKB.valW_eq (k : BKB) (hok : k.okB = true) (fa : ℕ → FE2) (m b : List FE2) (hm : m.length = 20)
    (hb : b.length = 21) : k.valW fa m b = (k.ents.map (qv fa (eqAtF m) (eqAtF b))).sum := by
  simp only [BKB.okB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hc, hβa⟩, hβb⟩, hnb⟩ := hok
  have hc2 := hc
  simp only [CTpl.okB, Bool.and_eq_true, decide_eq_true_eq] at hc2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hbb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc2
  have ha' : k.a + k.L ≤ 20 := by simpa [BKB.toCTpl] using ha
  have hbb' : k.bb + k.L ≤ 21 := by simpa [BKB.toCTpl] using hbb
  unfold BKB.valW BKB.ents
  rw [class_eq fa m b k.toCTpl (by simp only [BKB.toCTpl]; omega) (by simp only [BKB.toCTpl]; omega) hc,
    clsCombF_eq]
  simp only [BKB.toCTpl, sglCov_ents, List.map_nil, List.sum_nil]
  rw [k.V0_eq fa _ _ (by simp [hm]; omega) (by simp [hb]; omega) hnb]
  rfl

end Lvm6.V
