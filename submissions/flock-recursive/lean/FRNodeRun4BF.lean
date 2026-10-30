-- New for `flock-recursive` (IMPC2 §7 step 3; track IMPC2b): `SlotRunA` from the residual `SlotRunB` on the
-- template with the bits folded, and `Gap4.imp` / `Gaps4` from it.
import FRNodeRun4BS
import FRNodeRows4RepF

/-!
# `Gap4.imp` with the bits' run facts discharged

* **`SlotRunB`**: `SlotRunA` less what the template's rows now give on the run: the `bits n` auxiliary
  imports, the `bitOf` imports a `selectHalf` uses (`impBX`), IMPC's zero-pinned flags (`zPin`) and the
  statement's tag and zero-tail flags (`stFlag`).
* **`slotRunA_of_bits`**: `SlotRunA` from `SlotRunB`, given the template's `impcTG` and `bitTGB` rows,
  their holding at the slot, `PfCells`, `StmtBits` and `PosBits`.
* **`gap4Imp_of_bitsR`**: IMPC2's `gap4Imp_of_bitsB` with `SlotRunB` in place of `SlotRunA`; `StmtBits` and
  `PosBits` come from the decomposition rows (`stmtBits_of_glob`, `posBits_of_glob`).
* the certificate-level form (statement reads, siblings and the closure folded) is `FRNodeRun4CT.gaps4_of_runC`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## The template-free context's auxiliary imports -/

theorem tplExt4_tw_aux (F : TFilt) (R : ShR) (tp tp' : Tpl.TKey → Tpl.Tpl) (cb : Tpl.TKey → ℕ → ℕ) (P : Params) (cs : CS)
    (j r : ℕ) :
    (tplExt4 F R ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.aux =
      (tplExt4 F R ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.aux := by
  have h1 : (tplExt4S F R ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.aux =
      (tplExt4S F R ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.aux := by
    simp only [tplExt4S, tplExtF, tplExt]
    rcases cs.slot r with _ | ⟨_ | _ | _ | _ | _ | n, lr⟩ <;> try rfl
    by_cases hn : n ≤ logNMax <;> simp [hn, Option.filter, tplOut]
    try (split <;> rfl)
  have h2 : (tplExtKM F ⟨tp, cb⟩ P cs (.tensorW j r)).map Out.aux =
      (tplExtKM F ⟨tp', cb⟩ P cs (.tensorW j r)).map Out.aux := by
    simp only [tplExtKM]
    rcases Circ.akS (cs.slotK r .L32) with _ | a <;> rcases Circ.akS (cs.slotK r .P30) with _ | b <;>
      rcases Circ.akS (cs.slotK r .N30) with _ | c <;> try rfl
    simp only
    split <;> rfl
  simp only [tplExt4, Ext.orElse]
  cases h : tplExt4S F R ⟨tp, cb⟩ P cs (.tensorW j r) <;>
    cases h' : tplExt4S F R ⟨tp', cb⟩ P cs (.tensorW j r) <;> rw [h, h'] at h1 <;>
    simp only [Option.map] at h1 <;> try (cases h1)
  · simp only [Option.orElse]; split
    · simp only [Ext.orElse, extGetK]
      cases h3 : tplExtKM F ⟨tp, cb⟩ P cs (.tensorW j r) <;>
        cases h4 : tplExtKM F ⟨tp', cb⟩ P cs (.tensorW j r) <;> rw [h3, h4] at h2 <;>
        simp_all [Option.orElse]
    · rfl
  · simp_all [Option.orElse]

/-- **At a `tensorW`, `XofA`'s auxiliary imports are the compile's.** -/
theorem xofA_aux (π : ℕ) (P : Params) (cs : CS) (j r : ℕ) :
    (stepOut (XofA π) P cs (.tensorW j r)).aux = (stepOut (Xof π) P cs (.tensorW j r)).aux := by
  have h := tplExt4_tw_aux (protoF π) (protoR π) (fun _ => ⟨[], []⟩) (protoLay π).ctx.tpl (protoLay π).cb P cs j r
  show ((tplExt4A (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩ (colA π) P cs (.tensorW j r)).getD _).aux =
    ((tplExt4A (protoF π) (protoR π) ⟨(protoLay π).ctx.tpl, (protoLay π).cb⟩ (colA π) P cs (.tensorW j r)).getD _).aux
  rw [tplExt4A_ne (by simp), tplExt4A_ne (by simp)]
  show ((tplExt4 (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩ P cs (.tensorW j r)).getD _).aux =
    ((tplExt4 (protoF π) (protoR π) ⟨(protoLay π).ctx.tpl, (protoLay π).cb⟩ P cs (.tensorW j r)).getD _).aux
  generalize tplExt4 (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩ P cs (.tensorW j r) = A at h ⊢
  generalize tplExt4 (protoF π) (protoR π) ⟨(protoLay π).ctx.tpl, (protoLay π).cb⟩ P cs (.tensorW j r) = B at h ⊢
  cases A <;> cases B <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
  · rfl
  · exact h

/-! ## The residual -/

/-- A `bits` auxiliary import. -/
def isBitsA (a : (List Lin × ℕ × AuxK) × ℕ) : Bool :=
  match a.1.2.2 with
  | .bits _ => true
  | .felems _ => false

/-- Prototype `π`'s residual imports less the bits' (`impBX`). -/
def impBP (rt : RT) (A : AT) (π : ℕ) : List ℕ :=
  impBX (Xof π) (protoP π) rt A (CS.init (baseR π)) (protoProg π).ops

/-- **The residual run facts with the bits'** (`SlotRunA` less the `bits` auxiliary imports, the bit
imports `impBX` drops, the zero-pinned flags and the statement's flags). -/
def SlotRunB (rt : RT) (A : AT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∀ s : St, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
    (∀ a ∈ (protoCS π).aux, isBitsA a = false →
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ impBP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, zPin (pvP π) p = false → stFlag (bitTabP π) p = false →
      flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

theorem bitTabP_rt (π : ℕ) : (bitTabP π).rt = riAcc 0 (protoProg π).ops #[] := rfl

/-- **`SlotRunA` from the residual** `SlotRunB`, with `impcTG`'s and `bitTGB`'s rows in the template
(`hcI`/`hrI`, `hcB`/`hrB`), the template's rows holding at the slot, `PfCells`, and the statement's and
the answers' bits. -/
theorem slotRunA_of_bits {rt : RT} {A : AT} {impl : OpImpl} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace}
    {w : Asg} {Xa : Ext}
    (hlen : ∀ c op, (stepOut (Xof π) (protoP π) c op).slots.length = op.nOut)
    (hXa : ∀ c j r, (stepOut Xa (protoP π) c (.tensorW j r)).aux = (stepOut (Xof π) (protoP π) c (.tensorW j r)).aux)
    (hcI : ∀ op, impcCov op = true → A.cov op = true)
    (hrI : ∀ P c pre a act k, ∀ r ∈ impcRows (Xof π) π (pvP π) P c (.assertZero a act),
      r ∈ A.rows P c pre (.assertZero a act) k)
    (hcB : ∀ op, bitCovB op = true → A.cov op = true)
    (hrB : ∀ c pre op k, ∀ r ∈ bitRowsB (bitTabP π) Xa π (protoP π) c pre op k, r ∈ A.rows (protoP π) c pre op k)
    (hsel : SelOk w (protoP π) ι) (hask : ∀ r ∈ askRowsP A π, r.Holds w) (hpc : PfCells w π inp)
    (hS : StmtBits (bitTabP π) w π inp.π) (hPB : PosBits (bitTabP π) w π ι tr)
    (hres : SlotRunB rt A impl π ι inp tr w) : SlotRunA rt A impl π ι inp tr w := by
  intro s he
  obtain ⟨hx, hi, hf⟩ := hres s he
  have hone := hsel.1
  have hri : ∀ r, RIV ι inp tr s.regs ((bitTabP π).rt.getD r .none) (rd s.regs r) := by
    rw [bitTabP_rt]
    exact execA_ri _ 0 #[] St.init (by simpa using he) rfl fun r => by simp [RIV]
  have hsrc := srcOk_of hri hS hPB
  refine ⟨fun a ha => ?_, fun i hi0 => ?_, fun p hp => ?_⟩
  · -- the auxiliary imports
    cases hb : isBitsA a
    · exact hx a ha hb
    · rcases trail_aux (Xof π) (protoP π) A _ _ none 0 ha with h0 | ⟨c, pre', k', op, hcs, hm, hr⟩
      · cases h0
      obtain ⟨⟨cells, r, kd⟩, m⟩ := a
      cases kd with
      | felems _ => simp [isBitsA] at hb
      | bits n =>
        have htw := xof_bits hm rfl
        cases op <;> simp only [isTensorW, reduceCtorEq] at htw
        rename_i j r'
        have hcov := hcB (.tensorW j r') rfl
        have hrows : ∀ x ∈ bitRowsB (bitTabP π) Xa π (protoP π) c pre' (.tensorW j r') k', x.Holds w :=
          fun x hx0 => hask x (hr hcov x (hrB _ _ _ _ x hx0))
        simp only [bitRowsB] at hrows
        split_ifs at hrows with himp
        · exact absurd (hrows _ List.mem_cons_self) (failRT_not hone)
        rw [hXa] at hrows
        have := aux_bits (m := c.slots.size) hsel hsrc fun x hx0 => hrows x (auxBRows_mem hm x hx0)
        simpa [hcs] using this
  · -- the imports
    by_cases hb : i ∈ impBP rt A π
    · exact hi i hb
    · exact impA_bits (Xa := Xa) hsel hlen (fun b x y => hcB _ rfl) hrB hsrc _ _ none 0 St.init tr he rfl hask
        i hi0 hb
  · -- the flags
    cases hz : zPin (pvP π) p
    · cases hst : stFlag (bitTabP π) p
      · exact hf p hp hz hst
      · exact flag_stmt hri hS hst
    · rcases trail_fors (Xof π) (protoP π) A _ _ none 0 hp with h0 | ⟨c, pre', k', hcs, hr⟩
      · cases h0
      obtain ⟨op, m⟩ := p
      cases op with
      | assertZero a act =>
        simp only [zPin] at hz
        split at hz
        · rename_i f o len hpr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
          obtain ⟨ham, hw⟩ := hz
          have hcov := hcI (.assertZero a act) rfl
          have hrow : ∀ x ∈ impcRows (Xof π) π (pvP π) (protoP π) c (.assertZero a act), x.Holds w :=
            fun x hx0 => hask x (hr hcov x (hrI _ _ _ a act _ x hx0))
          simp only [impcRows] at hrow
          split_ifs at hrow with himp
          · exact absurd (hrow _ List.mem_cons_self) (failRT_not hone)
          · simp only [zRows, hpr] at hrow
            rw [if_pos ⟨by simpa [hcs] using ham, hw⟩] at hrow
            have hprov : s.regs[a]? = some (.b (inp.π.extract (absOff f o) (absOff f o + len))) :=
              execA_prov _ _ _ he (by rw [← provLT_eq]; exact provOf_mem hpr)
            refine flag_zpin hsel hpc hw hprov ham fun t ht e he0 => ?_
            have := hrow _ (List.mem_filterMap.2 ⟨t, List.mem_range.2 ht, by rw [he0]; rfl⟩)
            simpa [Row.Holds] using this
        · cases hz
      | _ => simp [zPin] at hz

/-! ## At the node -/

theorem stepOut_len {impl : OpImpl} {tc : Tpl.TCtx} {X : Ext} {κ : Kind} (hX : ExtOkK impl tc X κ) (P : Params)
    (c : CS) (op : Op) : (stepOut X P c op).slots.length = op.nOut := by
  simp only [stepOut]
  cases h : X P c op with
  | none => exact opOut_len P c op
  | some o => exact (hX P c op o h).1

/-- **`bitTGB`'s rows are the template's** (`withBitsB`). -/
theorem bitsB_rows (π : ℕ) : ∀ c pre op k, ∀ r ∈ bitRowsB (bitTabP π) (XofA π) π (protoP π) c pre op k,
    r ∈ (withBitsB askAq π).rows (protoP π) c pre op k := by
  intro c pre op k r hr
  simp only [withBitsB, AT.addD, TG.toAT, bitTGB]
  by_cases hc : bitCovB op = true
  · simp only [hc, ↓reduceIte]; exact List.mem_append_left _ hr
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine List.mem_append_right _ ?_
    have : op.item?.isSome = true ∨ bitRowsB (bitTabP π) (XofA π) π (protoP π) c pre op k = [] := by
      cases op <;> simp [bitRowsB, bitCovB, Op.item?] at hc ⊢ <;> simp_all
    rcases this with h1 | h1
    · simp only [h1, ↓reduceIte]; exact hr
    · rw [h1] at hr; cases hr

/-- **`Gap4.imp` with the bits' run facts discharged**: IMPC2's `gap4Imp_of_bitsB` with `SlotRunB` (the
statement's and the answers' bits from the decomposition rows). -/
theorem gap4Imp_of_bitsR {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withBitsB askAq) κ v arR2, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunB (rt (protoOf κ v)) (withBitsB askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) := by
  have hone := one_of_pubCells hS.1.2.2.2.2
  have hE := hS.1.2.2.2.1
  refine gap4Imp_of_bitsB hT₀ hT hok hfoldR hfoldA hS fun v hv ι hι => ?_
  have hvs := active_lt X.pf4 hv
  have hask := askHolds_of (hfoldA v hvs) hE
  have hpc := pfCells_of_rows hS.1 hv
  have hX := tplExt4A_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base (protoOf_le' κ v) ι)
    (protoLay (protoOf κ v)) (colA (protoOf κ v))
  have hrB := bitsB_rows (protoOf κ v)
  have hg := seed_rows hrB hask
  have hB : ∀ c < arNb, slotAsg κ v w (bitC (protoOf κ v) c) = 0 ∨ slotAsg κ v w (bitC (protoOf κ v) c) = 1 :=
    fun c hc => bit_slot hone hE hvs hc
  have hpad := (wots_aggPad_of_rows X.pf4 hS.1).2
  refine slotRunA_of_bits (Xa := XofA (protoOf κ v)) (stepOut_len hX _)
    (fun c j r => xofA_aux _ _ c j r)
    (fun op hc => by simp [withBitsB, withImpc, AT.addD, AT.add, TG.toAT, impcTG, hc])
    (fun P c pre a act k r hr => by
      simp only [withBitsB, AT.addD, TG.toAT, bitTGB, bitCovB, withImpc, AT.add, impcTG, pvP] at hr ⊢
      exact List.mem_append_left _ (List.mem_append_right _ hr))
    (fun op hc => by simp [withBitsB, AT.addD, TG.toAT, bitTGB, hc]) hrB hι hask hpc
    (stmtBits_of_glob hι.1 hpc hB hg)
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

end N4s
end FR
