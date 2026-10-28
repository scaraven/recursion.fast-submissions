-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS` and the claims' bindings; stage R4e).
import FRSoundness4R4FrLc

/-!
# RS0's claim values and their bindings on an accepted run (P4b's `RejRS4`)

* **`rs_alpha4`**: `finRS`'s exported value `α_j` (the `zhat` register `j`) is P4b's `alphaL4 κ es j`:
  RS0's slices are the log's message at 326 (`msg_abs4`), the inner weights `rsW4` are `cwL4`
  (`eqZ` at `eqZS`, parameter `hZ`; L2's and S2's challenges by the views).
* **The bindings on the same registers**: Z's `α_Z = P^z*(λ)` (`relZ4` (ii), `lagrangeS`'s second
  value, **`z_bind4`**), Lc's `α_Lc = v_β` (`relLc4` (iii), **`lc_bind4`**), Sh's (`sh_bind_*`),
  E's `α_E` = E4 end's value (`relE4`, **`e_bind4`**).
* **`not_rejRS4_seg`**, **`not_rejRS4_node`**: `¬ RejRS4 (okRS4 oZ oLc4 (oSh4 wNS))`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

section F
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- A `zhat` register reads the same in every file. -/
theorem Fields4.fv_zh (hF : Fields4 impl p inp tr P y zh Rs Ex) {k : ℕ} (hk : k ≤ 12) (j : ℕ) :
    fv (Rs k) (zh.getD j 0) = fv (Rs 0) (zh.getD j 0) := by
  show (rd (Rs k) _).toF = (rd (Rs 0) _).toF
  rw [(hF.chain (Nat.zero_le k) hk).rd (getD_lt (lt_of_lt_of_le (hF.pos (by decide)) le_rfl) hF.zlt j)]

/-- `finRS`'s registers are named registers (abstract `fi`). -/
theorem hin_RS {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (κ : Kind) (P : FinP) : ∀ x ∈ rsRefs4 κ fi P, x < n := by
  intro x hx
  simp only [rsRefs4, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ((⟨q, -, rfl⟩ | rfl) | hx) | hx
  · exact getD_lt hn (fun x hx => hsk "RS1" x (List.mem_of_mem_drop hx)) _
  · exact headD_lt (hsk "Z2") hn
  · exact hsk "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take hx)))
  · exact hsk "S2" x (List.mem_of_mem_drop (List.mem_of_mem_take
      (List.mem_of_mem_drop (List.mem_of_mem_take hx))))

/-- **`finRS`'s exports hold `rsAlpha4`** on the skeleton's file. -/
theorem rs_vals4 (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    ∀ j < 4, fv (Rs 0) (zh.getD j 0) =
      rsAlpha4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P j := by
  obtain ⟨L₀, hL₀, h0⟩ := hF.rs
  obtain ⟨L, hL, hv, -⟩ := exec_gFinRS impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
    (#[] ++ y.1.toArray) P (hin_RS (fun name x hx => outsOf_lt4 hF.sk [] #[] name x hx)
      (skel_pos4 hF.sk) _ P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL₀.symm.trans hL))
  intro j hj
  rw [h0, hF.zh_eq]
  exact hv j hj

end F

/-! ## The claim values are `alphaL4` -/

section V
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
  {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **Z2's `λ` by name** is `lamL`. -/
theorem lam_view4 : fv R ((outsOf fi "Z2").headD 0) = lamL (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, hlam, -⟩ := uni_view4 h hn4 (by rw [e4])
  rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout, List.headD_cons]
  show (rd R _).toF = _
  rw [hR.rd (skeleton4_out_lt p h.ref 4 (b + (if p.d.node = true then 0 else 1) + 3) (by rw [hout]; simp)),
    hlam, show phStart4 4 + 1 = 14 by rw [phStart4, fsStarts4_eq]; rfl]
  rfl

end V

/-- **Claim `j`'s value is `alphaL4`** (for `eqZ` at `eqZS` and a kind whose `m` the finals and
the chain agree on). -/
theorem rs_alpha4 (hZ : ∀ a b, impl.eqZ a b = eqZS a b) {tr : Trace} {P : FinP}
    {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (hm : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m) (j : Fin 4)
    (hj : j.val < (P4b.rsPtsL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4))).length) :
    P4b.alphaL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) j = fv (Rs 0) (zh.getD j 0) := by
  rw [rs_vals4 hF j j.isLt, rsAlpha4, P4b.alphaL4, ← Fin.sum_univ_eq_sum_range]
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hS := hF.sk
  have hκ := CKind.m_mem (kindOfC es)
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : P4b.sL4 (kindOfC es) es j i = sv4 P.S inp j i := by
    rw [P4b.sL4, if_pos hj, P4b.sliceL4, hPS,
      msg_abs4 hS (by norm_num) (by norm_num) fsMsgs4_ends.2.2.2 (by
        have := i.isLt; have := j.isLt; simp only [rsOff]; omega)]
    rfl
  rw [hs]
  refine congrArg (· * _) ?_
  -- the inner weights
  obtain ⟨n8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  have hch := chals_view4 hS hfi hR n8 (by rw [e8]) phaseIx4_rounds.2.2.1 (a := 14) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have hle : P.kv.m p.tix - 14 ≤ 18 := by rw [hm]; omega
  obtain ⟨-, hrp⟩ := s2r_view4 hS hfi hR hle
  rcases j with ⟨_ | _ | _ | _ | j, hj4⟩
  · simp only [rsW4, P4b.cwL4, cwF]
    rw [hZ, lam_view4 hS hfi hR]; rfl
  · simp only [rsW4, P4b.cwL4, cwF]
    rw [ptF, List.map_take, hch]
    rfl
  · simp only [rsW4, P4b.cwL4, cwF]
    have e7 : ((chals fi "S2" P.S.s2).drop (P.kv.m p.tix - 14)).take 7 =
        (((chals fi "S2" seq4.s2).drop (P.kv.m p.tix - 14)).take 10).take 7 := by
      rw [hPS, List.take_take]; rfl
    rw [ptF, e7, List.map_take, hrp]
    simp only [P4b.xSL4, ← hm, ← List.map_take, List.take_range]
    rfl
  · simp only [rsW4, P4b.cwL4, cwF]
  · omega

/-! ## The bindings on the fields -/

section B
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **Z's binding** (`relZ4` (ii)): `α_Z = P^z*(λ)` (`lagrangeS`'s second value at its
specification). -/
theorem z_bind4 (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    P4a.oZ (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 0) (zh.getD 0 0)) := by
  have hrel := relZ4_of_fields hF
  simp only [relZ4, Bool.and_eq_true] at hrel
  have h2 := hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 0 (by decide)
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, -, h134, hmsg, -, -⟩ := uni_view4 hF.sk hn4 (by rw [e4])
  have h13 : phStart4 4 = 13 := by rw [phStart4, fsStarts4_eq]; rfl
  rw [h13] at hmsg h134
  have hreg : (outsOf fi "Z2").getD 2 0 = b + (if p.d.node = true then 0 else 1) + 134 := by
    rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout]; rfl
  rw [hreg, hE.rd (skeleton4_out_lt p hF.sk.ref 4 _ (by rw [hout]; simp)), h134,
    hLS _ _ _ (by simp [uniEs]), Impl.lagrangeSS] at h2
  have e1 : (fun k : Fin 64 => (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD k 0) =
      pzL (fsOf tr (itemsOf seq4)) := funext fun k => by
    simp only [pzL]; rw [hmsg k (by omega)]
    simp [uniEs, Array.getD_eq_getD_getElem?, List.getElem?_range (show k.val < 127 by omega)]
  rw [P4a.oZ, fv, val_eqv_f4 h2, pzStar]
  simp only [Val.toF, e1]
  rfl

/-- **Lc's binding** (`relLc4` (iii)): `α_Lc = v_β` (L3's values batched by `β`). -/
theorem lc_bind4 (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) :
    P4a.oLc4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 1) (zh.getD 1 0)) := by
  have hrel := relLc4_of_fields hF
  simp only [relLc4, Bool.and_eq_true] at hrel
  have h2 := val_eqv_f4 hrel.1.2
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 1 (by decide)
  obtain ⟨hn10, e10⟩ := ph4 (n := 10) (x := ("L3β", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hβ⟩ := one_name_view4 hF.sk hfi hE hn10 (by rw [e10]) phaseIx_vals.2.2.2.2.2.1
  rw [show phStart4 10 = 98 by rw [phStart4, fsStarts4_eq]; rfl] at hβ
  rw [P4a.oLc4, fv]
  show (rd (Rs 1) (zh.getD 1 0)).toF = _
  rw [h2, lcV4_eq hF.sk hPS, hβ, vBetaL]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.drop_succ_cons,
    List.drop_zero, List.foldl_cons, List.foldl_nil, List.getD_cons_succ, List.getD_cons_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, vL, Val.toF, List.singleton_append]
  ring

/-- **`finE`'s relation on the fields of an accepted run** (field 4, file `Rs 4`; `lrEx` are
`finLr`'s exports). -/
theorem relE4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relE4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩ (Rs 4) P = true := by
  obtain ⟨hs3, L3, hL3, he3, hx3⟩ := hF.fld 3 (by decide)
  obtain ⟨-, L4, hL4, -, -⟩ := hF.fld 4 (by decide)
  rw [rest_gFinLr] at hL3 hx3
  rw [rest_gFinE] at hL4
  have hl3 := pureRun_len impl p.tix inp _ _ [] _ _ hL3
  rw [opsOut_gFinLr, List.length_nil, Nat.zero_add] at hl3
  have hsz4 : (Rs 4).size = (Rs 3).size + 14 := by rw [he3]; simp [hl3]
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩
  have hlr : ∀ j, lrEx fi j = (gFinLr P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3).size).2.getD j 0 :=
    lrEx_eq4 hs3 _ fi hx3
  obtain ⟨LE, hLE, -⟩ := flag_gFinE impl p.tix inp fi (Rs 4) P
    (hin_E (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide))
      (by rw [hlr]; show (Rs 3).size + 13 < _; omega) (by rw [hlr]; show (Rs 3).size + 4 < _; omega))
  exact pureRun_det hL4 hLE

/-- **E's binding** (`relE4`'s `e4`): `α_E` is E4 end's value. -/
theorem e_bind4 (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) :
    P4b.okE4 (fsOf tr (itemsOf seq4)) (fv (Rs 4) (zh.getD 3 0)) := by
  have hrel := relE4_of_fields hF
  have he4 : ((Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd (Rs 4) (zh.getD 3 0)) &&
      (inp.π.extract (fieldOffOf P.S fE + (gOE4end P.S + 16))
        (fieldOffOf P.S fE + (gOE4end P.S + 16) + 16)).data.all (· == 0)) = true := by
    revert hrel; simp only [relE4]; split <;> simp_all
  simp only [Bool.and_eq_true] at he4
  rw [P4b.okE4, fv, val_eqv_f4 he4.1, hPS,
    msg_abs4 hF.sk (by norm_num) (by norm_num) fsMsgs4_ends.2.2.1 (by norm_num), Nat.add_zero]
  rfl

end B

/-! ## `RejRS4` -/

/-- **`RejRS4` never holds on an accepted segment run** (`eqZ`, `lagrangeS`, `shiftTarget`,
`shiftMask`, `slotW`, `linkWAll` at the segment's specifications): every claim's value from RS0's
slices meets its binding (Z's `oZ`, Lc's `oLc4`, Sh's `oSh4 wNS` at `wSumSeg`). -/
theorem not_rejRS4_seg {σ : SegKind} {tr : Trace}
    (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = shiftSegS a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0)
    (wNS : CKind → Log → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4b.RejRS4 (P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 wNS)) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hk := kindOfC_seg4 hF.sk
  rintro ⟨-, j, hj, hne⟩
  apply hne
  rw [rs_alpha4 hZ hF rfl (by rw [hk]; rfl) j hj]
  rw [P4b.rsPtsL4_length, hk] at hj
  rcases j with ⟨_ | _ | _ | j, hj4⟩
  · exact z_bind4 hLS hF
  · rw [← hF.fv_zh (k := 1) (by decide)]; exact lc_bind4 hF rfl
  · rw [← hF.fv_zh (k := 2) (by decide)]; exact sh_bind_seg4 hST hSM hSW hLW hF wNS
  · simp only [CKind.isNode, Bool.false_eq_true, ite_false] at hj; omega

/-- **… nor on an accepted node run** (the node ops at `specN4`; Sh's binding at `wNS4`, E's
`okE4`). -/
theorem not_rejRS4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejRS4 (P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 P4a.wNS4)) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hk := kindOfC_node4 hF.sk
  rintro ⟨-, j, hj, hne⟩
  apply hne
  rw [rs_alpha4 hZ hF rfl (by rw [hk]; rfl) j hj]
  rcases j with ⟨_ | _ | _ | _ | j, hj4⟩
  · exact z_bind4 hLS hF
  · rw [← hF.fv_zh (k := 1) (by decide)]; exact lc_bind4 hF rfl
  · rw [← hF.fv_zh (k := 2) (by decide)]; exact sh_bind_node4 hST hSM hSW hLW hF
  · rw [← hF.fv_zh (k := 4) (by decide)]; exact e_bind4 hF rfl
  · omega

end FR.Snd.R4
