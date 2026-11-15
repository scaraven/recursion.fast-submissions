-- New for lvm2 E2-FT (E2F-C5): the small shape's tails at S2GF, circuit side: the tape's row claim's tail
-- (`LvmE2QPinOpen.rowTailG`) is V's `rowTailE2` (the switched target of the tail slices), and a `D` word half's tail
-- (`prepZ`'s `mass·zF`) is V's `tailDE2`.
import LvmE2QPinOpenS
import LvmQRingRowSem
import LvmE2QWSem

/-!
# The small shape's tails

* `trace_bit`: `Σ_k (δ_i a)^(2^k)` is bit `i` of `a` (the trace-dual basis, `dual_trace`, `fk_eq_sum_bits`);
  **`lrho_bits`**: the `ν`-pairing of the Frobenius powers of `u`'s coordinates is `Σ_j ρ_j·bit_j(u)`.
* `rowWordD_eq`: row `j` of the slices is `Σ_i bit_j(s_i)·x^i`; **`rowTailE2_eq`**: V's row tail is
  `Σ_l z*_l·L_ρ(w_l)`, `w_l = mass(z)·(1 + z₂₂)·eq((z₂₀, z₂₁), l)`.
* **`rowTailG_spec`**: the circuit's `rowTailG` is `rowTailE2`; **`tailD_val`**: `mass·zF(sel(l))` is `tailDE2`'s.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset

/-! ## Bits through the trace -/

/-- A bit as a `K` element. -/
def bitK (b : Bool) : FK := if b then 1 else 0

theorem bitK_pow (b : Bool) (k : ℕ) : bitK b ^ 2 ^ k = bitK b := by
  cases b
  · show (0 : FK) ^ 2 ^ k = 0; exact zero_pow (pow_ne_zero k two_ne_zero)
  · show (1 : FK) ^ 2 ^ k = 1; exact one_pow _

/-- **The trace against the dual basis is a bit**: `Σ_k (δ_i a)^(2^k) = bit_i(a)`. -/
theorem trace_bit {i : ℕ} (hi : i < 64) (a : FK) :
    ∑ k ∈ range 64, (dualK i * a) ^ 2 ^ k = bitK (a.val.toNat.testBit i) := by
  have ea : a = ∑ i' ∈ range 64, bitK (a.val.toNat.testBit i') * FK.x ^ i' := by
    conv_lhs => rw [fk_eq_sum_bits a]
    refine sum_congr rfl fun i' _ => ?_
    by_cases h : a.val.toNat.testBit i' <;> simp [h, bitK]
  have e1 : ∀ k, (dualK i * a) ^ 2 ^ k = ∑ i' ∈ range 64, bitK (a.val.toNat.testBit i') * (dualK i * FK.x ^ i') ^ 2 ^ k :=
    fun k => by
      conv_lhs => rw [ea, mul_sum, ← frobK_apply, map_sum]
      refine sum_congr rfl fun i' _ => ?_
      rw [frobK_apply, show dualK i * (bitK (a.val.toNat.testBit i') * FK.x ^ i') =
        bitK (a.val.toNat.testBit i') * (dualK i * FK.x ^ i') by ring, mul_pow, bitK_pow]
  rw [sum_congr rfl fun k _ => e1 k, sum_comm]
  rw [sum_congr rfl fun i' hi' => by rw [← mul_sum, dual_trace hi (mem_range.mp hi')]]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range, hi, ite_true]

/-- A bit of an `E2` value as an `E3` scalar. -/
def bE (u : FE2) (j : ℕ) : FE := FE.ofK (bitK (bitFE2 u j))

/-- **The `ν`-pairing of the Frobenius powers is the bit pairing**: `Σ_k ν₀_k a^(2^k) + ν₁_k b^(2^k) =
Σ_{j<128} ρ_j·bit_j(a + bX)`. -/
theorem lrho_bits (ρ : ℕ → FE) (u : FE2) :
    ∑ k ∈ range 64, (nuH ρ false k * FE.ofK (u.re ^ 2 ^ k) + nuH ρ true k * FE.ofK (u.im ^ 2 ^ k)) =
      ∑ j ∈ range 128, ρ j * bE u j := by
  have h1 : ∀ (h : Bool) (a : FK), ∑ k ∈ range 64, nuH ρ h k * FE.ofK (a ^ 2 ^ k) =
      ∑ i ∈ range 64, ρ (i + if h then 64 else 0) * FE.ofK (bitK (a.val.toNat.testBit i)) := by
    intro h a
    simp only [nuH, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [← trace_bit (mem_range.mp hi), show FE.ofK (∑ k ∈ range 64, (dualK i * a) ^ 2 ^ k) =
      ∑ k ∈ range 64, FE.ofK ((dualK i * a) ^ 2 ^ k) from map_sum FE.ofKRingHom _ _, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [dK, mul_pow, show FE.ofK (dualK i ^ 2 ^ k * a ^ 2 ^ k) = FE.ofK (dualK i ^ 2 ^ k) * FE.ofK (a ^ 2 ^ k) from
      map_mul FE.ofKRingHom _ _]
    ring
  have a1 : ∑ i ∈ range 64, ρ (i + if false = true then 64 else 0) * FE.ofK (bitK (u.re.val.toNat.testBit i)) =
      ∑ i ∈ range 64, ρ i * bE u i :=
    sum_congr rfl fun i hi => by simp [bE, bitFE2, mem_range.mp hi]
  have a2 : ∑ i ∈ range 64, ρ (i + if true = true then 64 else 0) * FE.ofK (bitK (u.im.val.toNat.testBit i)) =
      ∑ i ∈ range 64, ρ (64 + i) * bE u (64 + i) :=
    sum_congr rfl fun i _ => by simp [bE, bitFE2, Nat.add_comm i 64]
  rw [sum_add_distrib, h1, h1, a1, a2]
  exact (sum_range_add (fun j => ρ j * bE u j) 64 64).symm

/-! ## The row words -/

/-- Bit `j` of an `E2` value as a `K` element, additive. -/
def bitHom (j : ℕ) : FE2 →+ FK where
  toFun u := bitK (bitFE2 u j)
  map_zero' := by
    unfold bitFE2
    split_ifs
    · show bitK ((0 : UInt64).toNat.testBit j) = 0; simp [bitK]
    · show bitK ((0 : UInt64).toNat.testBit (j - 64)) = 0; simp [bitK]
  map_add' a b := by
    have hx : ∀ (p q : Bool), bitK (xor p q) = bitK p + bitK q := by decide
    rw [← hx]
    congr 1
    unfold bitFE2
    split_ifs
    · show (a.re.val ^^^ b.re.val).toNat.testBit j = _
      rw [UInt64.toNat_xor, Nat.testBit_xor]
    · show (a.im.val ^^^ b.im.val).toNat.testBit (j - 64) = _
      rw [UInt64.toNat_xor, Nat.testBit_xor]

theorem bitHom_apply (j : ℕ) (u : FE2) : bitHom j u = bitK (bitFE2 u j) := rfl

/-- **Row `j` of the slices** packs bit `j` of each slice. -/
theorem rowWordD_eq (sv : List FE2) (j : ℕ) :
    rowWordD sv j = ∑ i ∈ range 64, bitK (bitFE2 (sv.getD i 0) j) * FK.x ^ i := by
  have hv : (rowWordD sv j).val.toNat = natsum (fun i => bitFE2 (sv.getD i 0) j) 64 := by
    show ((natsum (fun i => bitFE2 (sv.getD i 0) j) 64).toUInt64).toNat = _
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (natsum_lt _ 64)]
  conv_lhs => rw [fk_eq_sum_bits (rowWordD sv j)]
  refine sum_congr rfl fun i hi => ?_
  rw [hv, testBit_natsum]
  simp only [mem_range.mp hi, decide_true, Bool.true_and]
  by_cases h : bitFE2 (sv.getD i 0) j <;> simp [h, bitK]

/-- The tail rows' lane weights: `w_l = mass(z)·eq(z₂₂, 0)·eq((z₂₀, z₂₁), l)`. -/
def wT (z : List FE2) (l : ℕ) : FE2 :=
  tailMassE2 z * E2V.eqEvalF (z.drop 22) (E2V.selPtF 0 (CMain.nu20 - 22)) *
    (E2V.eqKernelF ((z.drop 20).take 2)).getD l 0

theorem zStarF_c0 (l : ℕ) : (Shape.zStarF l).c₀ = zK l := by rw [← ofK_zK]; rfl

/-- **A row word of the tail slices**: `Σ_l z*_l·bit_j(w_l)`. -/
theorem rowWordD_tail (z : List FE2) (j : ℕ) :
    FE.ofK (rowWordD (tailSlicesE2 z) j) = ∑ l ∈ range 4, FE.ofK (zK l) * bE (wT z l) j := by
  have hs : ∀ i < 64, bitK (bitFE2 ((tailSlicesE2 z).getD i 0) j) =
      ∑ l ∈ range 4, if (zK l).val.toNat.testBit i then bitK (bitFE2 (wT z l) j) else 0 := by
    intro i hi
    have e : (tailSlicesE2 z).getD i 0 = ∑ l ∈ range 4,
        if (zK l).val.toNat.testBit i then wT z l else 0 := by
      unfold tailSlicesE2
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some]
      rw [E2V.sumF_eq_sum, lsum_range, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [zStarF_c0]
      unfold wT
      split_ifs <;> simp [List.getD_eq_getElem?_getD]
    rw [← bitHom_apply, e, map_sum]
    refine sum_congr rfl fun l _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hw : rowWordD (tailSlicesE2 z) j = ∑ l ∈ range 4, bitK (bitFE2 (wT z l) j) * zK l := by
    rw [rowWordD_eq, sum_congr rfl fun i hi => by rw [hs i (mem_range.mp hi), sum_mul], sum_comm]
    refine sum_congr rfl fun l _ => ?_
    conv_rhs => rw [fk_eq_sum_bits (zK l), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hw, show FE.ofK (∑ l ∈ range 4, bitK (bitFE2 (wT z l) j) * zK l) =
    ∑ l ∈ range 4, FE.ofK (bitK (bitFE2 (wT z l) j) * zK l) from map_sum FE.ofKRingHom _ _]
  refine sum_congr rfl fun l _ => ?_
  rw [show FE.ofK (bitK (bitFE2 (wT z l) j) * zK l) = FE.ofK (bitK (bitFE2 (wT z l) j)) * FE.ofK (zK l) from
    map_mul FE.ofKRingHom _ _, bE, mul_comm]

/-- **V's row tail** is `Σ_l z*_l·L_ρ(w_l)` (`L_ρ(w) = Σ_j ρ_j bit_j(w)`). -/
theorem rowTailE2_eq (eqR : List FE) (z : List FE2) :
    rowTailE2 eqR z = ∑ l ∈ range 4, FE.ofK (zK l) * ∑ j ∈ range 128, eqR.getD j 0 * bE (wT z l) j := by
  unfold rowTailE2
  dsimp only
  rw [sumE_eq, lsum_range, sum_congr rfl fun j _ => by rw [rowWordD_tail, mul_sum], sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-! ## The circuit's row tail -/

section Circ

variable {c : Ctx} {M : Mem}

theorem g2Mul_K (a b d : C2) : Hs c M (g2Mul a b d) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2Lin_K (k : FK) (k' : FE2) (a b : C2) : Hs c M (g2Lin k k' a b) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2One_K (a : C2) : Hs c M (g2One a) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2Add_K (a b : C2) : Hs c M (g2Add a b) KC2 := fun _ _ => ⟨rfl, rfl⟩

theorem hs_mapB_all {α β : Type} (f : α → BM β) (P : β → Prop) (hf : ∀ a, Hs c M (f a) P) :
    ∀ l : List α, Hs c M (mapB f l) (fun rs => ∀ x ∈ rs, P x)
  | [] => hs_pure (by simp)
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB_all f P hf l) fun rs hrs =>
    hs_pure fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hrs x hx

theorem hs_g2Eq0_K (z : C2) : ∀ (acc : C2) (rs : List C2), KC2 acc → Hs c M (g2Eq0 z acc rs) KC2
  | acc, [], h => hs_pure h
  | acc, r :: rs, _ => hs_bind (hs_g2One r) fun r1 _ => hs_bind (g2Mul_K acc r1 z) fun a ha =>
    hs_g2Eq0_K z a rs ha

theorem hs_g2EqStep_K (z : C2) (tab : List C2) (r : C2) : Hs c M (g2EqStep z tab r) (fun t => ∀ x ∈ t, KC2 x) := by
  unfold g2EqStep
  exact hs_bind (hs_g2One r) fun r1 _ => hs_bind (hs_mapB_all _ KC2 (fun e => g2Mul_K e r1 z) tab) fun lo hlo =>
    hs_bind (hs_mapB_all _ KC2 (fun e => g2Mul_K e r z) tab) fun hi hhi => hs_pure fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hlo x hx
      · exact hhi x hx

theorem hs_g2EqTab_K (z : C2) : ∀ (tab pt : List C2), (∀ x ∈ tab, KC2 x) →
    Hs c M (g2EqTab z tab pt) (fun t => ∀ x ∈ t, KC2 x)
  | tab, [], h => hs_pure h
  | tab, r :: rs, _ => hs_bind (hs_g2EqStep_K z tab r) fun t ht => hs_g2EqTab_K z t rs ht

theorem eqStep2_mul (a : FE2) (tab : List FE2) (r : FE2) :
    eqStep2 (tab.map (a * ·)) r = (eqStep2 tab r).map (a * ·) := by
  simp only [eqStep2, List.map_append, List.map_map, Function.comp_def, mul_assoc]

theorem foldl_eqStep2_mul (a : FE2) : ∀ (pt tab : List FE2),
    pt.foldl eqStep2 (tab.map (a * ·)) = (pt.foldl eqStep2 tab).map (a * ·)
  | [], _ => rfl
  | r :: pt, tab => by
    rw [List.foldl_cons, List.foldl_cons, eqStep2_mul, foldl_eqStep2_mul a pt]

/-- **`L_ρ` in the circuit** (`lRhoG`): `Σ_k ν₀_k·u_re^(2^k) + ν₁_k·u_im^(2^k)`. -/
theorem lRhoG_spec {F : FCtx} (hF : FCtxOk M F) (nu : RowNu) (u : C2) :
    Hs c M (lRhoG F nu u) (fun r => r.val M = ∑ k ∈ range 64, ((nu.nu0.getD k default).val M * u.re.val M ^ 2 ^ k +
      (nu.nu1.getD k default).val M * u.im.val M ^ 2 ^ k)) := by
  unfold lRhoG
  refine hs_bind (hs_frobsK hF.zk u.re) fun fr hfr => hs_bind (hs_frobsK hF.zk u.im) fun fi hfi => ?_
  have hgen : ∀ n, Hs c M ((List.range n).foldl (fun (m : BM Cell) k => m >>= fun acc =>
      mulAdd .E (nu.nu0.getD k default) (fr.getD k default) acc >>= fun a1 =>
      mulAdd .E (nu.nu1.getD k default) (fi.getD k default) a1) (pure F.z))
      (fun r => r.val M = ∑ k ∈ range n, ((nu.nu0.getD k default).val M * (fr.getD k default).val M +
        (nu.nu1.getD k default).val M * (fi.getD k default).val M)) := by
    intro n
    induction n with
    | zero => exact hs_pure (by rw [hF.z, sum_range_zero])
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine hs_bind ih fun acc hacc => hs_bind (hs_mulAdd _ _ _ _) fun a1 ha1 =>
        hs_mono (hs_mulAdd _ _ _ _) fun r hr => ?_
      rw [hr, ha1, hacc, sum_range_succ]
      ring
  refine hs_mono (hgen 64) fun r hr => ?_
  rw [hr]
  refine sum_congr rfl fun k hk => ?_
  rw [hfr k (mem_range.mp hk), hfi k (mem_range.mp hk)]

/-- **`L_ρ` of a `K`-celled value** is the bit pairing. -/
theorem lRho_val (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) {u : C2} (hu : KC2 u) :
    ∑ k ∈ range 64, ((nu.nu0.getD k default).val M * u.re.val M ^ 2 ^ k +
      (nu.nu1.getD k default).val M * u.im.val M ^ 2 ^ k) =
      ∑ j ∈ range 128, eqR.getD j 0 * bE (u.val M) j := by
  rw [← lrho_bits]
  refine sum_congr rfl fun k hk => ?_
  rw [(hnu k (mem_range.mp hk)).1, (hnu k (mem_range.mp hk)).2, ← kcell_val hu.1, ← kcell_val hu.2,
    show FE.ofK ((u.re.val M).c₀) ^ 2 ^ k = FE.ofK ((u.re.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm,
    show FE.ofK ((u.im.val M).c₀) ^ 2 ^ k = FE.ofK ((u.im.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm]
  rfl

theorem fe2_sub (a b : FE2) : a - b = a + b := rfl

theorem getD_of_map_eq {α β γ : Type} (f : α → γ) (g : β → γ) {as : List α} {bs : List β}
    (h : as.map f = bs.map g) {i : ℕ} (hi : i < bs.length) (da : α) (db : β) :
    f (as.getD i da) = g (bs.getD i db) := by
  have hl : as.length = bs.length := by simpa using congrArg List.length h
  have e := List.getElem_of_eq h (by simpa [hl] using hi)
  simp only [List.getElem_map] at e
  rw [List.getD_eq_getElem _ _ (hl ▸ hi), List.getD_eq_getElem _ _ hi, e]

theorem eqKernelF_eq (pt : List FE2) : E2V.eqKernelF pt = pt.foldl eqStep2 [1] := rfl

theorem c2_getD (z : List C2) {i : ℕ} (hi : i < z.length) : (z.getD i default).val M = (z.map (C2.val M)).getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem drop22 (zv : List FE2) (hz : zv.length = 23) : zv.drop 22 = [zv.getD 22 0] := by
  apply List.ext_getElem (by simp [hz])
  intro i h1 _
  have : i = 0 := by simp [hz] at h1; omega
  subst this
  simp [List.getD_eq_getElem?_getD, hz]

theorem take2drop20 (zv : List FE2) (hz : zv.length = 23) : (zv.drop 20).take 2 = [zv.getD 20 0, zv.getD 21 0] := by
  apply List.ext_getElem (by simp [hz])
  intro i h1 _
  have : i < 2 := by simp [hz] at h1; omega
  interval_cases i <;> simp [List.getD_eq_getElem?_getD, hz]

/-- **The circuit's row tail is V's** (`rowTailG` = `rowTailE2` at the claim's point; `κ = (1 + z₁₈)(1 + z₁₉)`). -/
theorem rowTailG_spec {F : FCtx} (hF : FCtxOk M F) (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR)
    (z : List C2) (hz : z.length = 23) (κ : C2) (hκ : κ.val M = kapE (z.map (C2.val M))) :
    Hs c M (rowTailG F nu z κ) (fun r => r.val M = rowTailE2 eqR (z.map (C2.val M))) := by
  unfold rowTailG
  refine hs_bind (hs_and (hs_g2One κ) (g2One_K κ)) fun mass ⟨hm, hmK⟩ => ?_
  refine hs_bind (hs_and (hs_g2Eq0 hF.z2 mass (z.drop 22)) (hs_g2Eq0_K F.z2 mass (z.drop 22) hmK))
    fun mb ⟨hmb, hmbK⟩ => ?_
  refine hs_bind (hs_and (hs_g2EqTab hF.z2 [mb] [z.getD 20 default, z.getD 21 default])
    (hs_g2EqTab_K F.z2 [mb] _ (by simpa using hmbK))) fun us ⟨hus, husK⟩ => ?_
  refine hs_bind (hs_mapBC (lRhoG F nu) (fun u => ∑ j ∈ range 128, eqR.getD j 0 * bE (u.val M) j) us
    fun u hu => hs_mono (lRhoG_spec hF nu u) fun r hr => by rw [hr, lRho_val nu eqR hnu (husK u hu)]) fun Ls hLs => ?_
  refine hs_mono (hs_linSumE F.z _) fun r hr => ?_
  have hzl : (z.map (C2.val M)).length = 23 := by simp [hz]
  have hus' : us.map (C2.val M) =
      (E2V.eqKernelF [(z.map (C2.val M)).getD 20 0, (z.map (C2.val M)).getD 21 0]).map (mb.val M * ·) := by
    rw [hus, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil, c2_getD z (by omega),
      c2_getD z (by omega), show [mb.val M] = [1].map (mb.val M * ·) by simp, foldl_eqStep2_mul, eqKernelF_eq]
  have hkl : ∀ a b : FE2, (E2V.eqKernelF [a, b]).length = 4 := fun a b => by simp [E2V.eqKernelF]
  have hul : us.length = 4 := by have := congrArg List.length hus'; rw [List.length_map, List.length_map, hkl] at this; exact this
  have ewG : ∀ l, mb.val M * (E2V.eqKernelF [(z.map (C2.val M)).getD 20 0, (z.map (C2.val M)).getD 21 0]).getD l 0 =
      wT (z.map (C2.val M)) l := by
    intro l
    rw [hmb, hm, hκ, List.map_drop, drop22 _ hzl, wT, drop22 _ hzl, take2drop20 _ hzl]
    have ea : E2V.eqAtF [(z.map (C2.val M)).getD 22 0] 0 = 1 + (z.map (C2.val M)).getD 22 0 := by
      simp [E2V.eqAtF]
    have eb : E2V.eqEvalF [(z.map (C2.val M)).getD 22 0] (E2V.selPtF 0 (CMain.nu20 - 22)) =
        1 + (z.map (C2.val M)).getD 22 0 := by
      rw [show CMain.nu20 - 22 = 1 from rfl, show (E2V.selPtF 0 1 : List FE2) = [0] from rfl]
      simp [E2V.eqEvalF]
    rw [ea, eb, tailMassE2, kapE, fe2_sub, fe2_sub, fe2_sub]
  rw [hr, hF.z, zero_add, rowTailE2_eq, List.map_map, lsum_range]
  refine sum_congr rfl fun l hl => ?_
  have hl4 := mem_range.mp hl
  have e1 := getD_of_map_eq (Cell.val M) _ hLs (by omega : l < us.length) default default
  have e2 := getD_of_map_eq (C2.val M) _ hus' (by rw [hkl]; exact hl4) default 0
  simp only [Function.comp_apply]
  rw [e1, e2, ewG]

end Circ

end Lvm.Q2
