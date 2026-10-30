-- New for `flock-recursive` (IMPC2 §7 step 3 item 1, the statement reads; track IMPC2b): `ATImp` of the unaligned
-- statement reads (`bitTGS`), and `Gap4.imp` / `Gaps4` with them folded beside the bits (phase 2a).
import FRNodeRun4BF

/-!
# The unaligned statement reads

An unaligned statement read (`piElem`/`piElemK`/`piDigest` inside the statement, off its element
boundaries) is an import whose value is a function of the input alone, so it is an `ATImp` class:

* **`rdWin_ev`**: with `StmtBits`, a window's row (`Σ e_j·s(b0 + j)` over the statement's bit cells, the
  tail bits zero) evaluates to the window's 16 bytes;
* **`atImp_bitS`**: `bitTGS`'s rows bind each covered read's import slots to its value;
* **`gap4Imp_of_bitsS`**: `Gap4.imp` with `bitTGB` and `bitTGS` folded (`withBitsS`, the fold a hypothesis);
  what remains per slot is `SlotRunB`. The certificate-level form is `FRNodeRun4CT.gaps4_of_runC`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## A window's value -/

/-- **An unaligned window's row evaluates to its bytes** (statement bits from `b0 = 8·(o' − so)`). -/
theorem rdWin_ev {T : BTab} {w : Asg} {π : ℕ} {q : ByteArray} (hS : StmtBits T w π q) {s : StSpec}
    (hs : T.st = some s) {o' : ℕ} (hso : s.so ≤ o') (hok : rdOk T (8 * (o' - s.so)) = true) :
    Lin.ev w (bitsLin (rdCells T π (8 * (o' - s.so)))) = F.ofBytes (bytesAt q o' 16) := by
  set b0 := 8 * (o' - s.so) with hb0
  have hL1 : ∀ p ∈ rdCells T π b0, p.1 < 128 ∧ ∃ c, T.stCell (b0 + p.1) = some (some c) ∧ p.2 = bitC π c := by
    intro p hp
    obtain ⟨j', hj', hf⟩ := List.mem_filterMap.1 hp
    split at hf
    · rename_i c hc
      cases hf; exact ⟨List.mem_range.1 hj', c, hc, rfl⟩
    · cases hf
  have hLb : ∀ p ∈ rdCells T π b0, w p.2 = 0 ∨ w p.2 = 1 := by
    intro p hp
    obtain ⟨-, c, hc, hp2⟩ := hL1 p hp
    have := hS.2 _ _ hc
    simp only [SrcV] at this
    rw [hp2, this]; cases stBit T q (b0 + p.1) <;> simp [Circ.bitF]
  have hnd : ((rdCells T π b0).map Prod.fst).Nodup := nodup_fst_filterMap _ List.nodup_range _ fun j y hy => by
    split at hy
    · cases hy; rfl
    · cases hy
  rw [bitsLin_eq fun p hp => (hL1 p hp).1]
  apply F.eq_of_bit
  intro j hj
  rw [bit_bitsLin w _ hLb (fun p hp => (hL1 p hp).1) hnd j hj, F.bit_ofBytes _ hj]
  simp only [bytesAt, Vector.getElem_ofFn]
  have hst : ∀ b, stBit T q b = (byteAt q (s.so + b / 8)).toNat.testBit (b % 8) := fun b => by
    simp only [stBit, hs]
  have hbit : stBit T q (b0 + j) = (byteAt q (o' + j / 8)).toNat.testBit (j % 8) := by
    rw [hst, show s.so + (b0 + j) / 8 = o' + j / 8 by omega, show (b0 + j) % 8 = j % 8 by omega]
  rw [← hbit]
  have hsome : (T.stCell (b0 + j)).isSome = true := List.all_eq_true.1 hok j (List.mem_range.2 hj)
  cases hc : T.stCell (b0 + j) with
  | none => rw [hc] at hsome; cases hsome
  | some x =>
    have hsv := hS.2 _ _ hc
    cases x with
    | none =>
      simp only [SrcV] at hsv
      rw [hsv, decide_eq_false_iff_not]
      rintro ⟨p, hp, rfl, -⟩
      obtain ⟨-, c, hc', -⟩ := hL1 p hp
      rw [hc] at hc'; cases hc'
    | some c =>
      simp only [SrcV] at hsv
      have hmem : (j, bitC π c) ∈ rdCells T π b0 :=
        List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, by rw [hc]⟩
      cases hb : stBit T q (b0 + j)
      · rw [decide_eq_false_iff_not]
        rintro ⟨p, hp, rfl, hw⟩
        obtain ⟨-, c', hc', hp2⟩ := hL1 p hp
        rw [hc] at hc'; cases hc'
        rw [hp2, hsv, hb] at hw
        simp [Circ.bitF] at hw
      · rw [decide_eq_true_iff]
        exact ⟨_, hmem, rfl, by rw [hsv, hb]; rfl⟩

/-- **A covered read's rows**: its slot is `[some (t, ls)]`, `n` forms, each its window's bytes. -/
theorem stRd_rep {T : BTab} {P : Params} {w : Asg} {π : ℕ} {q : ByteArray} (hone : P.one.ev w = 1)
    (hS : StmtBits T w π q) {sl : List Slot} {t : Ty} {o n : ℕ} (hwin : T.stWin o n = true)
    (hrows : ∀ r ∈ stRdRowsS T P π sl t o n, r.Holds w) :
    ∃ ls : List Lin, sl = [some (t, ls)] ∧ ∃ hl : ls.length = n, ∀ c (hc : c < n),
      (ls[c]'(hl ▸ hc)).ev w = F.ofBytes (bytesAt q (o + 16 * c) 16) := by
  unfold BTab.stWin at hwin
  unfold stRdRowsS at hrows
  split at hwin
  · rename_i s hs
    rw [hs] at hrows
    simp only [decide_eq_true_eq] at hwin
    split at hrows
    · rename_i t' ls heq
      simp only [Option.some.injEq] at heq
      subst heq
      split_ifs at hrows with hg
      · obtain ⟨rfl, hl⟩ := hg
        refine ⟨ls, rfl, hl, fun c hc => ?_⟩
        have hmem : (ls[c]'(hl ▸ hc), c) ∈ ls.zipIdx := by
          rw [List.mem_iff_getElem?]; exact ⟨c, by simp [List.getElem?_zipIdx, hl ▸ hc]⟩
        have hr := hrows _ (List.mem_map.2 ⟨_, hmem, rfl⟩)
        dsimp only at hr
        split at hr
        · rename_i hok
          simp only [Row.Holds, hone, one_mul, ev_subN, Lin.ev_nil] at hr
          rw [sub_eq_zero.1 hr, rdWin_ev hS hs (by omega) hok]
        · exact absurd hr (failRT_not hone)
      · exact absurd (hrows _ List.mem_cons_self) (failRT_not hone)
    · exact absurd (hrows _ List.mem_cons_self) (failRT_not hone)
  · cases hwin

/-! ## `ATImp` of the statement reads -/

/-- **`ATImp` of the statement reads' generator** (`bitTGS`, read off an extension `Xa` agreeing with the
compile's at its reads), given `StmtBits`. -/
theorem atImp_bitS {impl : OpImpl} {X Xa : Ext} {π : ℕ} {T : BTab} {κ : Kind} {inp : Input} {w : Asg}
    (hX : ∀ P cs op, bitCovS T op = true → stepOut Xa P cs op = stepOut X P cs op)
    (hS : StmtBits T w π inp.π) : ATImp impl X (bitTGS Xa π T).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  have hone := hc.1.1
  have hr := hc.2.2.2
  have hcv : bitCovS T op = true := hcov
  have hx := hX P cs op hcv
  simp only [TG.toAT, bitTGS] at hr
  cases op <;> simp only [bitCovS, reduceCtorEq, Bool.false_eq_true] at hcv
  · -- `piElem`
    rename_i f o
    simp only [bitRowsS, hcv, if_true, hx] at hr
    obtain ⟨ls, hsl, hl, hv⟩ := stRd_rep hone hS hcv hr
    simp only [evalOp, Res.vals.injEq] at hev; obtain ⟨rfl, -⟩ := hev
    rw [hsl]
    refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    obtain ⟨l0, rfl⟩ : ∃ l0, ls = [l0] := by
      match ls, hl with | [l0], _ => exact ⟨l0, rfl⟩
    have := hv 0 (by norm_num)
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
    simp [encV, this]
  · -- `piElemK`
    rename_i f o
    simp only [bitRowsS, hcv, if_true, hx] at hr
    obtain ⟨ls, hsl, hl, hv⟩ := stRd_rep hone hS hcv hr
    simp only [evalOp, Res.vals.injEq] at hev; obtain ⟨rfl, -⟩ := hev
    rw [hsl]
    refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    obtain ⟨l0, l1, rfl⟩ : ∃ l0 l1, ls = [l0, l1] := by
      match ls, hl with | [l0, l1], _ => exact ⟨l0, l1, rfl⟩
    have h0 := hv 0 (by norm_num)
    have h1 := hv 1 (by norm_num)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    simp only [List.map_cons, List.map_nil, encV, encK, K.ofBytes, h0, h1, bytesAt_lo, bytesAt_hi]
  · -- `piDigest`
    rename_i f o
    simp only [bitRowsS, hcv, if_true, hx] at hr
    obtain ⟨ls, hsl, hl, hv⟩ := stRd_rep hone hS hcv hr
    simp only [evalOp, Res.vals.injEq] at hev; obtain ⟨rfl, -⟩ := hev
    rw [hsl]
    refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    obtain ⟨l0, l1, rfl⟩ : ∃ l0 l1, ls = [l0, l1] := by
      match ls, hl with | [l0, l1], _ => exact ⟨l0, l1, rfl⟩
    have h0 := hv 0 (by norm_num)
    have h1 := hv 1 (by norm_num)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    simp only [List.map_cons, List.map_nil, encV, dlo, dhi, digestAt_eq, h0, h1, bytesAt_lo, bytesAt_hi]

/-- **At a statement read, `XofA`'s output is the compile's.** -/
theorem xofA_read (π : ℕ) {T : BTab} (P : Params) (cs : CS) (op : Op) (hop : bitCovS T op = true) :
    stepOut (XofA π) P cs op = stepOut (Xof π) P cs op := by
  cases op <;> simp only [bitCovS, reduceCtorEq, Bool.false_eq_true] at hop <;>
    simp only [stepOut, XofA, Xof, tplExt4, tplExt4S, Ext.orElse, tplExtKM, tplExtF, tplExt, extGetK,
      Option.orElse, Option.filter]

/-! ## The node's template with the statement reads -/

/-- **The node's template with the bits and the statement reads** (phase 2a of the `askTG` fold). -/
def withBitsS (Aq : ℕ → AT) (π : ℕ) : AT := (withBitsB Aq π).addD (bitTGS (XofA π) π (bitTabP π)).toAT

/-- **`bitTGB`'s rows are the template's** (`withBitsS`). -/
theorem bitsS_rowsB (π : ℕ) : ∀ c pre op k, ∀ r ∈ bitRowsB (bitTabP π) (XofA π) π (protoP π) c pre op k,
    r ∈ (withBitsS askAq π).rows (protoP π) c pre op k := by
  intro c pre op k r hr
  have hB := bitsB_rows π c pre op k r hr
  simp only [withBitsS, AT.addD, TG.toAT, bitTGS]
  by_cases hc : bitCovS (bitTabP π) op = true
  · exfalso
    cases op <;> simp only [bitCovS, reduceCtorEq, Bool.false_eq_true] at hc <;> simp [bitRowsB] at hr
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_append_left _ hB

/-- **`Gap4.imp` with the bits' run facts and the statement reads discharged**: from the replay
(`RepOk`, its fold), the fold of `withBitsS`, `StmtN4R` and, at every active slot and selectable index,
the residual `SlotRunB` over `withBitsS`. -/
theorem gap4Imp_of_bitsS {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withBitsS askAq) κ v arR2, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunB (rt (protoOf κ v)) (withBitsS askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) := by
  have hone := one_of_pubCells hS.1.2.2.2.2
  have hE := hS.1.2.2.2.1
  refine gap4Imp_of_runS hT₀ hT hok (fun e tr => X.pfHdr_reassemble4 e tr)
    (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) hfoldR hfoldA hS.1 fun v hv ι hι => ?_
  have hvs := active_lt X.pf4 hv
  have hask := askHolds_of (hfoldA v hvs) hE
  have hpc := pfCells_of_rows hS.1 hv
  have hX := tplExt4_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base (protoOf_le' κ v) ι)
    (protoLay (protoOf κ v))
  have hrB := bitsS_rowsB (protoOf κ v)
  have hg := seed_rows hrB hask
  have hB : ∀ c < arNb, slotAsg κ v w (bitC (protoOf κ v) c) = 0 ∨ slotAsg κ v w (bitC (protoOf κ v) c) = 1 :=
    fun c hc => bit_slot hone hE hvs hc
  have hpad := (wots_aggPad_of_rows X.pf4 hS.1).2
  have hSt := stmtBits_of_glob hι.1 hpc hB hg
  refine ⟨atOk_addD (atOk_addD (atOk_add (atOk_add (atOk_add (atOk_askT _ hS.1 hv hι)
      (atImp_inp (inpCells_of_rows (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr)
        (fun e tr => X.pfHdr_reassemble4 e tr) hS.1 v hv ι hι)))
      (atImp_rsv_slot hS.2.1 hS.2.2 v ι _)) (atImp_impc (pfCells_of_rows hS.1 hv)))
      (atImp_bitB (xofA_imp _))) (atImp_bitS (fun P cs op hop => xofA_read _ P cs op hop) hSt), ?_⟩
  refine slotRunA_of_bits (Xa := XofA (protoOf κ v)) (stepOut_len hX _)
    (fun c j r => xofA_aux _ _ c j r)
    (fun op hc => by simp [withBitsS, withBitsB, withImpc, AT.addD, AT.add, TG.toAT, impcTG, hc])
    (fun P c pre a act k r hr => by
      simp only [withBitsS, withBitsB, AT.addD, TG.toAT, bitTGS, bitTGB, bitCovS, bitCovB, withImpc, AT.add,
        impcTG, pvP] at hr ⊢
      simp [hr])
    (fun op hc => by simp [withBitsS, withBitsB, AT.addD, TG.toAT, bitTGB, hc]) hrB hι hask hpc hSt
    (posBits_of_glob hι (fun k v h => mkTab_ans h) hB hg fun k it e hit he => ?_) (h v hv ι hι)
  rw [itemsT_get] at hit
  obtain ⟨hkn, rfl⟩ := itAt_of hit
  have ha0 : aElT k (itAt k) = ansE k := by rw [aElT, offT_get hkn.le]; rfl
  have hs := itOff_slen hkn
  have hal := ans_al hkn
  obtain ⟨h1, h2⟩ := slot_ans' hv hpad hkn he
  rw [ha0, arC, a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), arC,
    a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), h1, h2]
  exact ⟨rfl, rfl⟩

-- `askFold_bitsS`, `gap4Imp_rtC1cS`, `gaps4_of_runS` (FOLD2's fold, by `rfl`) are removed: `askTG` now also folds
-- the siblings and the closure (track SIB); their replacements are `FRNodeRun4CT.askFold_close`,
-- `gap4Imp_rtC1cC`, `gaps4_of_runC`.

/-! ## Controls -/

namespace BitRunCtl

/-- A toy table: register 0 the statement's first byte (`π[48]`), register 1 the tag constant `78`. -/
def T0 (tag : UInt8) : BTab := ⟨#[.pf 48 1, .cb ⟨#[tag]⟩, .pf 113 15], #[], #[], #[], 0, some ⟨48, 78, 65, 80⟩⟩

/-- (+) **`stFlag`**: the tag check and the zero tail are the statement's flags; (−) a constant other than
the tag, an operand registered after the flag, or a tail read off the tail are not. -/
theorem stFlag_ctl : stFlag (T0 78) (.assertEq 0 1 allK, 2) = true ∧ stFlag (T0 78) (.assertZero 2 allK, 3) = true ∧
    stFlag (T0 77) (.assertEq 0 1 allK, 2) = false ∧ stFlag (T0 78) (.assertEq 0 1 allK, 1) = false ∧
    stFlag (T0 78) (.assertZero 0 allK, 3) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- (+) **`bitNx`**: a `bitOf` whose next op is a `selectHalf` on its result; (−) on another register, or
another next op. -/
theorem bitNx_ctl : bitNx (.bitOf 3 0) [.selectHalf 5 1 2] 5 = true ∧ bitNx (.bitOf 3 0) [.selectHalf 4 1 2] 5 = false ∧
    bitNx (.bitOf 3 0) [.bitOf 3 1] 5 = false := ⟨rfl, rfl, rfl⟩

/-- (+) **`riOf`'s guards**: an `idx` on an earlier register is recorded; (−) on a later one it is not, nor
is a byte constant that differs between kinds. -/
theorem riOf_ctl :
    (match riOf 0 2 (.idx (fun _ => 1) (fun _ => 4) (fun _ => 0)) with | [.idx ..] => true | _ => false) = true ∧
    (match riOf 0 2 (.idx (fun _ => 5) (fun _ => 4) (fun _ => 0)) with | [.none] => true | _ => false) = true ∧
    (match riOf 0 2 (.const fun κ => .b ⟨#[if κ = .L32 then 1 else 2]⟩) with | [.none] => true | _ => false) = true := by
  refine ⟨rfl, rfl, ?_⟩; decide

end BitRunCtl

end N4s
end FR
