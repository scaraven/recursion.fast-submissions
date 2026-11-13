-- New for lvm2 roll 11 (M′, R11-X): the barycentric interpolation's semantics with the positions below any `P`
-- (the shipped `2^15`). Adapted from `LvmXInterp4.lean` (`BaryLay`, `sValK`, `sLoop_sem`, `baryIR_sem`,
-- `baryIR_interp`), `LvmXInterp3.lean` (`ycell_lt`) and `LvmXInterp.lean` (`baryValK_eq`), `2^15` → `P`;
-- `sBody_sem` and everything below it are reused.
import LvmXInterp4

/-!
# The interpolation at positions below `P`

* `BaryLayP P …`: `BaryLay` with the column store `cb + cs·j + c` over `j < P` (the targets `k ≤ P`);
* **`baryIR_semP`**, **`baryIR_interpP`**: `out[c][s] = interpF ptK Jl.toFinset y_c s` for `Jl` without repeats
  below `P` (`P ≤ 2^64`), `s < |Jl|`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM runPrims

theorem ycell_ltP {P cs j c : ℕ} (hj : j < P) (hc : c < cs) : cs * j + c < cs * P := by
  have : cs * (j + 1) ≤ cs * P := Nat.mul_le_mul_left cs hj
  rw [Nat.mul_succ] at this; omega

/-- **The machine's value is the interpolation** (`J ⊆ [0, P)` listed without repeats,
`s < P`). -/
theorem baryValK_eqP {P : ℕ} (hP : P ≤ 2 ^ 64) {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < P) {s : ℕ}
    (hs : s < P) (y : ℕ → BF64) :
    baryValK Jl Jl.length s y = interpF ptK Jl.toFinset y s := by
  have hinj : Set.InjOn ptK (Jl.toFinset : Set ℕ) := fun a ha b hb h =>
    ptK_injOn64 (Set.mem_Iio.2 ((hJ a (List.mem_toFinset.1 ha)).trans_le hP))
      (Set.mem_Iio.2 ((hJ b (List.mem_toFinset.1 hb)).trans_le hP)) h
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  by_cases hsJ : s ∈ Jl
  · obtain ⟨t, ht, hts⟩ := List.mem_iff_getElem.1 hsJ
    have h0 : ellK Jl Jl.length s = 0 := by
      refine Finset.prod_eq_zero (i := t) (Finset.mem_range.2 ht) ?_
      rw [djK, List.getD_eq_getElem _ _ ht, hts, ← CharTwo.sub_eq_add, sub_self]
    rw [baryValK, if_pos h0, interpF_self hinj y (List.mem_toFinset.2 hsJ)]
  · have hne : ∀ m ∈ Jl.toFinset, ptK s ≠ ptK m := fun m hm h => hsJ (by
      have := ptK_injOn64 (Set.mem_Iio.2 (hs.trans_le hP))
        (Set.mem_Iio.2 ((hJ m (List.mem_toFinset.1 hm)).trans_le hP)) h
      rw [this]; exact List.mem_toFinset.1 hm)
    have h0 : ellK Jl Jl.length s ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      rw [djK, ← CharTwo.sub_eq_add, sub_ne_zero]
      exact hne _ (List.mem_toFinset.2 (hget t (Finset.mem_range.1 ht)))
    rw [baryValK, if_neg h0, interpF_bary hne, Algebra.algebraMap_self]
    simp only [RingHom.id_apply]
    rw [prod_toFinsetB hnd, sum_toFinsetB hnd]
    refine congrArg₂ _ (Finset.prod_congr rfl fun t _ => by rw [djK, CharTwo.sub_eq_add])
      (Finset.sum_congr rfl fun t ht => ?_)
    have ht' := Finset.mem_range.1 ht
    have hP : (∏ m ∈ range Jl.length, if m = t then 1 else djK Jl t + djK Jl m) =
        ∏ m ∈ range Jl.length, if Jl.getD m 0 = Jl.getD t 0 then 1
          else ptK (Jl.getD t 0) - ptK (Jl.getD m 0) := by
      refine Finset.prod_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.1 hm
      by_cases hmt : m = t
      · rw [if_pos hmt, if_pos (by rw [hmt])]
      · rw [if_neg hmt, if_neg (fun h => hmt ((hnd.getElem_inj_iff).1 (by
          rwa [List.getD_eq_getElem _ _ hm', List.getD_eq_getElem _ _ ht'] at h))), djK, djK,
          CharTwo.sub_eq_add]
    rw [eAtK, wgtK, prod_erase_iteB (List.mem_toFinset.2 (hget t ht')), prod_toFinsetB hnd, hP,
      djK, CharTwo.sub_eq_add (ptK s)]


/-- **The interpolation's layout** on a memory of `sz` words: the list `J` (`k` words at `jb`),
the tables `W` and `E` (`k` words at `wb`, `eb`), the output (`k·C` words at `ob`; coordinate `c`
of target `s` at `ob + k·c + s`) and the column store (`y_c(j)` at `cb + cs·j + c` for
`j < P`, `c < C ≤ cs`: inside `[cb, cb + cs·P)`). All lie above the registers and below
`2^64`; the written regions `W`, `E`, `O` lie inside the memory and are disjoint from each other
and from `J` and the column store (`J` and the store are only read and may overlap). -/
structure BaryLayP (P k C jb wb eb cb cs ob sz : ℕ) : Prop where
  tP : P < 2 ^ 64
  tC : C < 2 ^ 64
  kN : k ≤ P
  cC : C ≤ cs
  rJ : regs ≤ jb
  rW : regs ≤ wb
  rE : regs ≤ eb
  rO : regs ≤ ob
  rY : regs ≤ cb
  tJ : jb + k < 2 ^ 64
  tW : wb + k < 2 ^ 64
  tE : eb + k < 2 ^ 64
  tO : ob + k * C < 2 ^ 64
  tY : cb + cs * P < 2 ^ 64
  zW : wb + k ≤ sz
  zE : eb + k ≤ sz
  zO : ob + k * C ≤ sz
  dJW : jb + k ≤ wb ∨ wb + k ≤ jb
  dJE : jb + k ≤ eb ∨ eb + k ≤ jb
  dJO : jb + k ≤ ob ∨ ob + k * C ≤ jb
  dWE : wb + k ≤ eb ∨ eb + k ≤ wb
  dWO : wb + k ≤ ob ∨ ob + k * C ≤ wb
  dEO : eb + k ≤ ob ∨ ob + k * C ≤ eb
  dYW : cb + cs * P ≤ wb ∨ wb + k ≤ cb
  dYE : cb + cs * P ≤ eb ∨ eb + k ≤ cb
  dYO : cb + cs * P ≤ ob ∨ ob + k * C ≤ cb

/-- The value of target `s₀`, coordinate `c`, on the heap `M` (the list `J`, the table `W` and
the column store). -/
def sValKP (M : Mem) (k jb wb cb cs : ℕ) (x : ℕ → ℕ) (s0 c : ℕ) : BF64 :=
  if ∏ t ∈ range k, (ptK s0 + rdK M (jb + t)) = 0 then rdK M (cb + cs * s0 + c)
  else (∏ t ∈ range k, (ptK s0 + rdK M (jb + t))) *
    ∑ t ∈ range k, rdK M (cb + cs * x t + c) * (rdK M (wb + t) * (ptK s0 + rdK M (jb + t))⁻¹)

/-- **The target loop**: `out[c][s] = sValKP s c` for every `s < k`, `c < C`; the heap outside
the `E` row and the output rows is kept. -/
theorem sLoop_semP (I : Array Word) (s : St) (hM : Inv s.M)
    {P k C jb wb eb cb cs ob : ℕ} {x : ℕ → ℕ} (hL : BaryLayP P k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, x t < P) (hN : rd s.M bN1 = toWord k) (hS : rd s.M bS = toWord 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (.loopK bC1 bN1 (toWord k)
        (sBody k C jb wb eb cb cs ob)) s).M (ob + k * c + s0) =
      sValKP s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) →
      rd (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M y =
        rd s.M y) ∧
    Inv (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M := by
  obtain ⟨htP, htC, hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL
  have hk64 : k < 2 ^ 64 := by omega
  have hC64 : C < 2 ^ 64 := by omega
  have hcol : ∀ j' < P, ∀ c < C, cb + cs * j' + c < cb + cs * P := fun j' hj' c hc => by
    have := ycell_ltP hj' (show c < cs by omega); omega
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bS = toWord j ∧
    (∀ s0 < j, ∀ c < C, rdK st.M (ob + k * c + s0) = sValKP s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) → rd st.M y = rd s.M y)
  have ef : ∀ i, i ≠ bC1 → i ≠ cTmp → rd (entryK bC1 bN1 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC1) (n := bN1) (K := k) (sBody k C jb wb eb cb cs ob) Q s hM
    (by decide) (by decide) (by decide) hN hk64 ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hS],
      fun s0 hs0 => absurd hs0 (Nat.not_lt_zero _),
      fun y hy _ _ => ef y (by simp only [regs, bC1] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hS', hV, hH⟩
    simp only [regs] at rJ rW rE rO rY
    obtain ⟨b1, b2, b3, hM2⟩ := sBody_sem I st hM' (k := k) (C := C) (jb := jb) (wb := wb)
      (eb := eb) (cb := cb) (cs := cs) (ob := ob) (s0 := j) (x := x) hk64 hC64 hj
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) tJ tW tE
      (fun t ht c hc => by have := hcol _ (hJn t ht) c hc; omega)
      (fun c hc => by have := hcol j (by omega) c hc; omega)
      tO (by rw [hz]; exact zO) (by rw [hz]; exact zE) dJE dWE dJO.symm dEO.symm
      (fun c hc j' hj' => by
        have h' : j' < P := by
          rcases hj' with h' | rfl
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h'; exact hJn t (List.mem_range.1 ht)
          · omega
        have := hcol j' h' c hc
        exact ⟨by rcases dYO with h | h <;> omega, by rcases dYE with h | h <;> omega⟩) hS'
      (fun t ht => by
        rw [hH _ (by simp only [regs]; omega) (by rcases dJE with h | h <;> omega)
          (by rcases dJO with h | h <;> omega), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => ?_⟩
    · have hlt := out_ltB (k := k) hc (show s0 < k by omega)
      rw [rdK_congrB (rd_decS (by simp only [bC1]; omega) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs0 with hs0 | rfl
      · have hne : ∀ c' < C, ob + k * c + s0 ≠ ob + k * c' + j := fun c' _ => by
          have := cellB_ne (k := k) (c := c) (c' := c') (show s0 < k by omega) hj (by omega)
          omega
        rw [rdK_congrB (b3 _ (by simp only [regs]; omega) (by rcases dEO with h | h <;> omega) hne),
          hV s0 hs0 c hc]
      · rw [b1 c hc, sValKP]
        have hcl : ∀ j' < P, rdK st.M (cb + cs * j' + c) = rdK s.M (cb + cs * j' + c) :=
          fun j' hj' => rdK_congrB (hH _ (by simp only [regs]; omega)
            (by have := hcol j' hj' c hc; rcases dYE with h | h <;> omega)
            (by have := hcol j' hj' c hc; rcases dYO with h | h <;> omega))
        have hjt : ∀ t < k, rdK st.M (jb + t) = rdK s.M (jb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; omega) (by rcases dJE with h | h <;> omega)
            (by rcases dJO with h | h <;> omega))
        have hwt : ∀ t < k, rdK st.M (wb + t) = rdK s.M (wb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; omega) (by rcases dWE with h | h <;> omega)
            (by rcases dWO with h | h <;> omega))
        have hP : ∏ t ∈ range k, (ptK s0 + rdK st.M (jb + t)) =
            ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) :=
          Finset.prod_congr rfl fun t ht => by rw [hjt t (Finset.mem_range.1 ht)]
        rw [hP, hcl s0 (by omega)]
        split_ifs
        · rfl
        · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hcl _ (hJn t ht'), hwt t ht', hjt t ht']
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega)]
      rw [b3 y hy hy2 (fun c' hc' => by have := out_ltB (k := k) hc' hj; omega), hH y hy hy2 hy3]

/-! ## The whole program -/

/-- **The interpolation on the machine**: for the list `Jl` at `jb` (`k` entries below `P`)
and the column store at `cb`, `out[c][s] = baryValK Jl k s y_c` for every target `s < k` and
coordinate `c < C`, with `y_c(j)` the store's element `cb + cs·j + c`; the heap outside `W`, `E`
and the output rows is kept. -/
theorem baryIR_semP (I : Array Word) (s : St) (hM : Inv s.M)
    {P k C jb wb eb cb cs ob : ℕ} {Jl : List ℕ} (hL : BaryLayP P k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, Jl.getD t 0 < P)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (baryIR k C jb wb eb cb cs ob) s).M (ob + k * c + s0) =
        baryValK Jl k s0 (fun j => rdK s.M (cb + cs * j + c))) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → (y < eb ∨ eb + k ≤ y) →
      (y < ob ∨ ob + k * C ≤ y) → rd (semXIR I (baryIR k C jb wb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR k C jb wb eb cb cs ob) s).M := by
  have hL' := hL
  obtain ⟨htP, htC, hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL'
  have hk64 : k < 2 ^ 64 := by omega
  simp only [regs] at rJ rW rE rO rY
  rw [baryIR]
  simp only [semXIR_seq]
  -- `W`
  obtain ⟨w1, w2, hM1⟩ := wtIR_sem I s hM (k := k) (jb := jb) (wb := wb) (G := djK Jl) hk64
    (by simp only [regs]; omega) (by simp only [regs]; omega) tJ tW zW dJW
    (fun m hm => rdK_toWord (hJ m hm))
  have z1 := size_sem I (wtIR k jb wb) s
  generalize semXIR I (wtIR k jb wb) s = q1 at w1 w2 hM1 z1
  -- `s := 0`, `bN1 := k`
  have hs1 := hM1.1
  have p : rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M bS = toWord 0 ∧
      rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M bN1 = toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne] <;> rfl
  have p3 : ∀ i, i ≠ bS → i ≠ bN1 →
      rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M i = rd q1.M i :=
    fun i h1 h2 => by
      rw [sem_blk]
      exact rd_runPrims_of_not_writes (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM2 := inv_sem I (P := .blk [.const bS 0, .const bN1 (toWord k)]) (s := q1)
    (by simp [WF, Prim.dst, bS, bN1]) hM1
  have z2 := size_sem I (.blk [.const bS 0, .const bN1 (toWord k)]) q1
  generalize semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1 = q2 at p p3 hM2 z2
  have H2 : ∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (p3 y (by simp only [regs, bS] at hy ⊢; omega) (by simp only [regs, bN1] at hy ⊢; omega)).trans
      (w2 y hy hy2)
  have hL2 : BaryLayP P k C jb wb eb cb cs ob q2.M.size := by rw [z2, z1]; exact hL
  obtain ⟨l1, l2, hM3⟩ := sLoop_semP I q2 hM2 (x := fun t => Jl.getD t 0) hL2 hJn p.2 p.1
    (fun t ht => by
      rw [H2 _ (by simp only [regs]; omega) (by rcases dJW with h | h <;> omega), hJ t ht])
  refine ⟨fun s0 hs0 c hc => ?_, fun y hy hy1 hy2 hy3 => ?_, hM3⟩
  · rw [l1 s0 hs0 c hc, sValKP, baryValK]
    have hcl : ∀ j < P, rdK q2.M (cb + cs * j + c) = rdK s.M (cb + cs * j + c) := fun j hj =>
      rdK_congrB (H2 _ (by simp only [regs]; omega)
        (by have := ycell_ltP hj (show c < cs by omega); rcases dYW with h | h <;> omega))
    have hd : ∀ t < k, rdK q2.M (jb + t) = djK Jl t := fun t ht =>
      (rdK_congrB (H2 _ (by simp only [regs]; omega) (by rcases dJW with h | h <;> omega))).trans
        (rdK_toWord (hJ t ht))
    have hw : ∀ t < k, rdK q2.M (wb + t) = wgtK Jl k t := fun t ht =>
      (rdK_congrB (p3 _ (by simp only [bS]; omega) (by simp only [bN1]; omega))).trans (w1 t ht)
    have hP : ∏ t ∈ range k, (ptK s0 + rdK q2.M (jb + t)) = ellK Jl k s0 :=
      Finset.prod_congr rfl fun t ht => by rw [hd t (Finset.mem_range.1 ht)]
    rw [hP, hcl s0 (by omega)]
    by_cases h0 : ellK Jl k s0 = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hcl _ (hJn t ht'), hw t ht', hd t ht', eAtK]
  · rw [l2 y hy hy2 hy3, H2 y hy hy1]

/-- **The interpolation computed**: with `k = |Jl|`, `Jl` without repeats and below `P`,
every `out[c][s]` is `interpF ptK J y_c s` (`J = Jl.toFinset`, `y_c(j)` the element at
`cb + cs·j + c`). -/
theorem baryIR_interpP (I : Array Word) (s : St) (hM : Inv s.M)
    {P C jb wb eb cb cs ob : ℕ} {Jl : List ℕ}
    (hL : BaryLayP P Jl.length C jb wb eb cb cs ob s.M.size) (hnd : Jl.Nodup)
    (hJn : ∀ j ∈ Jl, j < P)
    (hJ : ∀ t < Jl.length, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    ∀ s0 < Jl.length, ∀ c < C,
      rdK (semXIR I (baryIR Jl.length C jb wb eb cb cs ob) s).M (ob + Jl.length * c + s0) =
      interpF ptK Jl.toFinset (fun j => rdK s.M (cb + cs * j + c)) s0 := by
  have hget : ∀ t < Jl.length, Jl.getD t 0 < P := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hJn _ (List.getElem_mem ht)
  intro s0 hs0 c hc
  rw [(baryIR_semP I s hM hL hget hJ).1 s0 hs0 c hc]
  exact baryValK_eqP (by have := hL.tP; omega) hnd hJn (by have := hL.kN; omega) _

end Lvm.X
