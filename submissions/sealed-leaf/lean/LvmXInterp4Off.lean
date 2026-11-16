/- `LvmXInterp4Off` (GOLF2 off-path move, group 22 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXInterp4,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXInterp4

-- ===== from `LvmXInterp4` =====

section
section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb

/-- **The machine's value is the interpolation** (`J ⊆ [0, 2^15)` listed without repeats,
`s < 2^15`). -/
theorem baryValK_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < 2 ^ 15) {s : ℕ}
    (hs : s < 2 ^ 15) (y : ℕ → BF64) :
    baryValK Jl Jl.length s y = interpF ptK Jl.toFinset y s := by
  have hinj : Set.InjOn ptK (Jl.toFinset : Set ℕ) := fun a ha b hb h =>
    ptK_injOn15 (Set.mem_Iio.2 (hJ a (List.mem_toFinset.1 ha)))
      (Set.mem_Iio.2 (hJ b (List.mem_toFinset.1 hb))) h
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  by_cases hsJ : s ∈ Jl
  · obtain ⟨t, ht, hts⟩ := List.mem_iff_getElem.1 hsJ
    have h0 : ellK Jl Jl.length s = 0 := by
      refine Finset.prod_eq_zero (i := t) (Finset.mem_range.2 ht) ?_
      rw [djK, List.getD_eq_getElem _ _ ht, hts, ← CharTwo.sub_eq_add, sub_self]
    rw [baryValK, if_pos h0, interpF_self hinj y (List.mem_toFinset.2 hsJ)]
  · have hne : ∀ m ∈ Jl.toFinset, ptK s ≠ ptK m := fun m hm h => hsJ (by
      have := ptK_injOn15 (Set.mem_Iio.2 hs)
        (Set.mem_Iio.2 (hJ m (List.mem_toFinset.1 hm))) h
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

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset
attribute [local irreducible] entryK storeM

theorem lo_invK {d a : ℕ} (h : d < regs) : Lo (invK d a) := fun p hp => by
  have := invKC_dst d a p hp; simp only [regs] at h ⊢; (clear * - h this; omega)

theorem loK_mul_iff {d a b : ℕ} (h : d < regs) : Lo (mulK d a b) ↔ True := iff_true_intro (lo_mulK h)
theorem loK_inv_iff {d a : ℕ} (h : d < regs) : Lo (invK d a) ↔ True := iff_true_intro (lo_invK h)

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset
attribute [local irreducible] entryK storeM

theorem wf_wInner (jb : ℕ) : WF (wInner jb) := by
  simp [wInner, addr1Ps, WF, Prim.dst, wfK_mul, bA, bK, fX, fDd, bZ, bM, fPr]

end Lvm.X
end
end

section
section
namespace Lvm.X
open RecursionFast Finset
attribute [local irreducible] entryK storeM

/-- A column cell lies in the column store. -/
theorem ycell_lt {cs j c : ℕ} (hj : j < 2 ^ 15) (hc : c < cs) : cs * j + c < cs * 2 ^ 15 := by
  have := lt_mulB (k := cs) hj; (clear * - hc this; omega)

end Lvm.X
end
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb
attribute [local irreducible] entryK storeM runPrims

/-- **The interpolation's layout** on a memory of `sz` words: the list `J` (`k` words at `jb`),
the tables `W` and `E` (`k` words at `wb`, `eb`), the output (`k·C` words at `ob`; coordinate `c`
of target `s` at `ob + k·c + s`) and the column store (`y_c(j)` at `cb + cs·j + c` for
`j < 2^15`, `c < C ≤ cs`: inside `[cb, cb + cs·2^15)`). All lie above the registers and below
`2^64`; the written regions `W`, `E`, `O` lie inside the memory and are disjoint from each other
and from `J` and the column store (`J` and the store are only read and may overlap). -/
structure BaryLay (k C jb wb eb cb cs ob sz : ℕ) : Prop where
  kN : k ≤ 2 ^ 15
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
  tY : cb + cs * 2 ^ 15 < 2 ^ 64
  zW : wb + k ≤ sz
  zE : eb + k ≤ sz
  zO : ob + k * C ≤ sz
  dJW : jb + k ≤ wb ∨ wb + k ≤ jb
  dJE : jb + k ≤ eb ∨ eb + k ≤ jb
  dJO : jb + k ≤ ob ∨ ob + k * C ≤ jb
  dWE : wb + k ≤ eb ∨ eb + k ≤ wb
  dWO : wb + k ≤ ob ∨ ob + k * C ≤ wb
  dEO : eb + k ≤ ob ∨ ob + k * C ≤ eb
  dYW : cb + cs * 2 ^ 15 ≤ wb ∨ wb + k ≤ cb
  dYE : cb + cs * 2 ^ 15 ≤ eb ∨ eb + k ≤ cb
  dYO : cb + cs * 2 ^ 15 ≤ ob ∨ ob + k * C ≤ cb

/-- The value of target `s₀`, coordinate `c`, on the heap `M` (the list `J`, the table `W` and
the column store). -/
def sValK (M : Mem) (k jb wb cb cs : ℕ) (x : ℕ → ℕ) (s0 c : ℕ) : BF64 :=
  if ∏ t ∈ range k, (ptK s0 + rdK M (jb + t)) = 0 then rdK M (cb + cs * s0 + c)
  else (∏ t ∈ range k, (ptK s0 + rdK M (jb + t))) *
    ∑ t ∈ range k, rdK M (cb + cs * x t + c) * (rdK M (wb + t) * (ptK s0 + rdK M (jb + t))⁻¹)

/-- **The target loop**: `out[c][s] = sValK s c` for every `s < k`, `c < C`; the heap outside
the `E` row and the output rows is kept. -/
theorem sLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob : ℕ} {x : ℕ → ℕ} (hL : BaryLay k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, x t < 2 ^ 15) (hN : rd s.M bN1 = toWord k) (hS : rd s.M bS = toWord 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (.loopK bC1 bN1 (toWord k)
        (sBody k C jb wb eb cb cs ob)) s).M (ob + k * c + s0) =
      sValK s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) →
      rd (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M y =
        rd s.M y) ∧
    Inv (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M := by
  obtain ⟨hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL
  have hk64 : k < 2 ^ 64 := by (clear * - hkN; omega)
  have hC64 : C < 2 ^ 64 := by (clear * - hcC tY; omega)
  have hcol : ∀ j' < 2 ^ 15, ∀ c < C, cb + cs * j' + c < cb + cs * 2 ^ 15 := fun j' hj' c hc => by
    have := ycell_lt hj' (show c < cs by (clear * - hcC hc; omega)); (clear * - this; omega)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bS = toWord j ∧
    (∀ s0 < j, ∀ c < C, rdK st.M (ob + k * c + s0) = sValK s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) → rd st.M y = rd s.M y)
  have ef : ∀ i, i ≠ bC1 → i ≠ cTmp → rd (entryK bC1 bN1 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC1) (n := bN1) (K := k) (sBody k C jb wb eb cb cs ob) Q s hM
    (by decide) (by decide) (by decide) hN hk64 ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hS],
      fun s0 hs0 => absurd hs0 (Nat.not_lt_zero _),
      fun y hy _ _ => ef y (by simp only [regs, bC1] at hy ⊢; (clear * - hy; omega))
        (by simp only [regs, cTmp] at hy ⊢; (clear * - hy; omega))⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hS', hV, hH⟩
    simp only [regs] at rJ rW rE rO rY
    obtain ⟨b1, b2, b3, hM2⟩ := sBody_sem I st hM' (k := k) (C := C) (jb := jb) (wb := wb)
      (eb := eb) (cb := cb) (cs := cs) (ob := ob) (s0 := j) (x := x) hk64 hC64 hj
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) tJ tW tE
      (fun t ht c hc => by have := hcol _ (hJn t ht) c hc; (clear * - tY this; omega))
      (fun c hc => by have := hcol j (by (clear * - hkN hj; omega)) c hc; (clear * - tY this; omega))
      tO (by rw [hz]; exact zO) (by rw [hz]; exact zE) dJE dWE dJO.symm dEO.symm
      (fun c hc j' hj' => by
        have h' : j' < 2 ^ 15 := by
          rcases hj' with h' | rfl
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h'; exact hJn t (List.mem_range.1 ht)
          · (clear * - hkN hj; omega)
        have := hcol j' h' c hc
        exact ⟨by rcases dYO with h | h <;> (clear * - this h hC64 hc; omega), by rcases dYE with h | h <;> (clear * - this h hC64 hc; omega)⟩) hS'
      (fun t ht => by
        rw [hH _ (by simp only [regs]; (clear * - rJ; omega)) (by rcases dJE with h | h <;> (clear * - ht h; omega))
          (by rcases dJO with h | h <;> (clear * - ht h; omega)), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => ?_⟩
    · have hlt := out_ltB (k := k) hc (show s0 < k by (clear * - hj hs0; omega))
      rw [rdK_congrB (rd_decS (by simp only [bC1]; (clear * - rO tO hlt; omega)) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs0 with hs0 | rfl
      · have hne : ∀ c' < C, ob + k * c + s0 ≠ ob + k * c' + j := fun c' _ => by
          have := cellB_ne (k := k) (c := c) (c' := c') (show s0 < k by (clear * - hj hs0; omega)) hj (by (clear * - hs0; omega))
          (clear * - this; omega)
        rw [rdK_congrB (b3 _ (by simp only [regs]; (clear * - rO; omega)) (by rcases dEO with h | h <;> (clear * - h hlt; omega)) hne),
          hV s0 hs0 c hc]
      · rw [b1 c hc, sValK]
        have hcl : ∀ j' < 2 ^ 15, rdK st.M (cb + cs * j' + c) = rdK s.M (cb + cs * j' + c) :=
          fun j' hj' => rdK_congrB (hH _ (by simp only [regs]; (clear * - rY tY; omega))
            (by have := hcol j' hj' c hc; rcases dYE with h | h <;> (clear * - this h hC64 hc; omega))
            (by have := hcol j' hj' c hc; rcases dYO with h | h <;> (clear * - this h hC64 hc; omega)))
        have hjt : ∀ t < k, rdK st.M (jb + t) = rdK s.M (jb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; (clear * - rJ; omega)) (by rcases dJE with h | h <;> (clear * - ht h; omega))
            (by rcases dJO with h | h <;> (clear * - ht h; omega)))
        have hwt : ∀ t < k, rdK st.M (wb + t) = rdK s.M (wb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; (clear * - rW; omega)) (by rcases dWE with h | h <;> (clear * - ht h; omega))
            (by rcases dWO with h | h <;> (clear * - ht h; omega)))
        have hP : ∏ t ∈ range k, (ptK s0 + rdK st.M (jb + t)) =
            ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) :=
          Finset.prod_congr rfl fun t ht => by rw [hjt t (Finset.mem_range.1 ht)]
        rw [hP, hcl s0 (by (clear * - hkN rO tO hlt hj; omega))]
        split_ifs
        · rfl
        · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hcl _ (hJn t ht'), hwt t ht', hjt t ht']
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; (clear * - hy; omega))]
      rw [b3 y hy hy2 (fun c' hc' => by have := out_ltB (k := k) hc' hj; (clear * - hy3 this; omega)), hH y hy hy2 hy3]

/-- **The interpolation on the machine**: for the list `Jl` at `jb` (`k` entries below `2^15`)
and the column store at `cb`, `out[c][s] = baryValK Jl k s y_c` for every target `s < k` and
coordinate `c < C`, with `y_c(j)` the store's element `cb + cs·j + c`; the heap outside `W`, `E`
and the output rows is kept. -/
theorem baryIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob : ℕ} {Jl : List ℕ} (hL : BaryLay k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, Jl.getD t 0 < 2 ^ 15)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (baryIR k C jb wb eb cb cs ob) s).M (ob + k * c + s0) =
        baryValK Jl k s0 (fun j => rdK s.M (cb + cs * j + c))) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → (y < eb ∨ eb + k ≤ y) →
      (y < ob ∨ ob + k * C ≤ y) → rd (semXIR I (baryIR k C jb wb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR k C jb wb eb cb cs ob) s).M := by
  have hL' := hL
  obtain ⟨hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL'
  have hk64 : k < 2 ^ 64 := by (clear * - hkN; omega)
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
        rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - h1 h2; omega)) _
  have hM2 := inv_sem I (P := .blk [.const bS 0, .const bN1 (toWord k)]) (s := q1)
    (by simp [WF, Prim.dst, bS, bN1]) hM1
  have z2 := size_sem I (.blk [.const bS 0, .const bN1 (toWord k)]) q1
  generalize semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1 = q2 at p p3 hM2 z2
  have H2 : ∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (p3 y (by simp only [regs, bS] at hy ⊢; (clear * - hy; omega)) (by simp only [regs, bN1] at hy ⊢; (clear * - hy; omega))).trans
      (w2 y hy hy2)
  have hL2 : BaryLay k C jb wb eb cb cs ob q2.M.size := by rw [z2, z1]; exact hL
  obtain ⟨l1, l2, hM3⟩ := sLoop_sem I q2 hM2 (x := fun t => Jl.getD t 0) hL2 hJn p.2 p.1
    (fun t ht => by
      rw [H2 _ (by simp only [regs]; (clear * - rJ; omega)) (by rcases dJW with h | h <;> (clear * - ht h; omega)), hJ t ht])
  refine ⟨fun s0 hs0 c hc => ?_, fun y hy hy1 hy2 hy3 => ?_, hM3⟩
  · rw [l1 s0 hs0 c hc, sValK, baryValK]
    have hcl : ∀ j < 2 ^ 15, rdK q2.M (cb + cs * j + c) = rdK s.M (cb + cs * j + c) := fun j hj =>
      rdK_congrB (H2 _ (by simp only [regs]; (clear * - rY tY; omega))
        (by have := ycell_lt hj (show c < cs by (clear * - hcC hc; omega)); rcases dYW with h | h <;> (clear * - this h; omega)))
    have hd : ∀ t < k, rdK q2.M (jb + t) = djK Jl t := fun t ht =>
      (rdK_congrB (H2 _ (by simp only [regs]; (clear * - rJ; omega)) (by rcases dJW with h | h <;> (clear * - ht h; omega)))).trans
        (rdK_toWord (hJ t ht))
    have hw : ∀ t < k, rdK q2.M (wb + t) = wgtK Jl k t := fun t ht =>
      (rdK_congrB (p3 _ (by simp only [bS]; (clear * - rW; omega)) (by simp only [bN1]; (clear * - rW; omega)))).trans (w1 t ht)
    have hP : ∏ t ∈ range k, (ptK s0 + rdK q2.M (jb + t)) = ellK Jl k s0 :=
      Finset.prod_congr rfl fun t ht => by rw [hd t (Finset.mem_range.1 ht)]
    rw [hP, hcl s0 (by (clear * - hkN hs0; omega))]
    by_cases h0 : ellK Jl k s0 = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hcl _ (hJn t ht'), hw t ht', hd t ht', eAtK]
  · rw [l2 y hy hy2 hy3, H2 y hy hy1]

/-- **The interpolation computed**: with `k = |Jl|`, `Jl` without repeats and below `2^15`,
every `out[c][s]` is `interpF ptK J y_c s` (`J = Jl.toFinset`, `y_c(j)` the element at
`cb + cs·j + c`). -/
theorem baryIR_interp (I : Array Word) (s : St) (hM : Inv s.M)
    {C jb wb eb cb cs ob : ℕ} {Jl : List ℕ}
    (hL : BaryLay Jl.length C jb wb eb cb cs ob s.M.size) (hnd : Jl.Nodup)
    (hJn : ∀ j ∈ Jl, j < 2 ^ 15)
    (hJ : ∀ t < Jl.length, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    ∀ s0 < Jl.length, ∀ c < C,
      rdK (semXIR I (baryIR Jl.length C jb wb eb cb cs ob) s).M (ob + Jl.length * c + s0) =
      interpF ptK Jl.toFinset (fun j => rdK s.M (cb + cs * j + c)) s0 := by
  have hget : ∀ t < Jl.length, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hJn _ (List.getElem_mem ht)
  intro s0 hs0 c hc
  rw [(baryIR_sem I s hM hL hget hJ).1 s0 hs0 c hc]
  exact baryValK_eq hnd hJn (by have := hL.kN; (clear * - hs0 this; omega)) _

/-- **lvm's instance** (`k = 2^13` positions, `C = 64` rows, the word `wd` at `wB + 64·q + t`):
row `t` of the output (at `ob + 2^13·t`) is the interpolation of the read word's leaf word `t` on
`J`, at the points `ptK s`, `s < 2^13`; the heap outside `W`, `E` and the output is kept. -/
theorem baryIR_lvm (I : Array Word) (s : St) (hM : Inv s.M) {jb wb eb wB ob : ℕ} {Jl : List ℕ}
    (hlen : Jl.length = 2 ^ 13) (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < 2 ^ 15)
    (hL : BaryLay (2 ^ 13) 64 jb wb eb wB 64 ob s.M.size)
    (hJ : ∀ t < 2 ^ 13, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < 2 ^ 13, ∀ t < 64,
      rdK (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M (ob + 2 ^ 13 * t + s0) =
      interpF ptK Jl.toFinset (fun j => rdK s.M (wB + 64 * j + t)) s0) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + 2 ^ 13 ≤ y) → (y < eb ∨ eb + 2 ^ 13 ≤ y) →
      (y < ob ∨ ob + 2 ^ 13 * 64 ≤ y) →
      rd (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M := by
  have hget : ∀ t < 2 ^ 13, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by (clear * - hlen ht; omega))]; exact hJn _ (List.getElem_mem _)
  have hb := baryIR_sem I s hM hL hget hJ
  refine ⟨fun s0 hs0 t ht => ?_, hb.2.1, hb.2.2⟩
  rw [hb.1 s0 hs0 t ht, ← hlen]
  exact baryValK_eq hnd hJn (by (clear * - hs0; omega)) _

end Lvm.X
end
