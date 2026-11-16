-- New for lvm2 E2-FT (E2F-V2-TOP): the top of statement 15 (`refinesF20`): `VSFX N` (V_S at S2GF) accepting on a
-- trace ⇒ the compiled verifier at S2GF's format `fmtF20` accepting, through the width-aware simulation (`simW`),
-- for any IOP verifier `PS` V_S's decision refines with read widths `rwF20` (roll 11's `refines_seqOfT`, read for
-- `VSFX`/`decideFFX` at the header `headerBytesP (P20F.withF accVF)`).
import LvmE2VParseF
import LvmE2VRefines
import LvmE2VRefW
import LvmCertF20

-- (GOLF2: 5 declarations that `certified` does not use moved verbatim to `LvmCertF20InstOff`, outside its import closure.)

/-!
# V_S ⇒ S.V at S2GF

* `decideFFX_ok`: `decideFFX` holds ⇒ the run from `RS.startH (headerBytesP p)` held its checks and `Φ_Q` holds.
* `RefDF N PS nR`: V_S's S2GF decision refines `PS x` with read widths `rwF20` (from read 0 to `nR`) on every
  stream whose public values are the statement's (`pubOfA accVF … = pubXF x`).
* **`refines_seqOfF`**: on every trace, from `RefDF`, `PS x` following the S2GF schedule's atoms (`Fol`), the
  schedule's static facts (`stA`) and its read widths (`WAt rwF20 0`).
* **`refinesF20_of`**: `refinesF20`'s conclusion (on every log) for `PSWithM (midP (midM reloc20 (midF₂ (N.inst Q
  lay))))` from those three facts.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

section Main

variable (N : TypedV.TNat) (PS : List UInt8 → VerifierProgram Bool) (nR : ℕ)

/-- **V_S ⇒ S.V on a trace at a stage** (`refines_seqOfF`'s proof, generic in the record `p`, the format `fmt`, the
decision `D` V_S drives (`VS = parseOk p, then drive p (D vk c)`), the decision program `prog` with its final check
`φ`, the statement predicate `Pre` the stream's header gives, and the format's occupied words `occ`): from the
decision refining `PS` (`href`), `PS x` following the schedule's atoms, the schedule's static facts and its read
widths. -/
theorem refines_seqOfGO (p : Params) (fmt : Lvm.ASM.SFmt) {occ : ℕ → ℕ → ℕ} (VS : Lvm.T.SProg)
    (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (prog : RecursionFast.Digest → RecursionFast.Digest → DM Acc) (φ : Acc → Prop)
    (Pre : ByteArray → RecursionFast.Digest → RecursionFast.Digest → List UInt8 → Prop)
    (hVS : ∀ vk c π, VS vk c π = if parseOk p vk c π then drive p π (D vk c) else .ret false)
    (hD : ∀ vk c sig, D vk c sig = true →
      (runD (prog vk c) sig (RS.startH (headerBytesP p))).2.ok = true ∧
        φ (runD (prog vk c) sig (RS.startH (headerBytesP p))).1)
    (hPre : ∀ vk c π sig, parseOk p vk c π = true →
      (∀ t < headerBytesP p - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      Pre sig vk c (xOfH (headerBytesP p) π))
    (href : ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), Pre sig vk c x →
      RefAtPW capS occ shpS fmt.rw sig 0 (prog vk c) (PS x) (fun _ b ↦ b = true) φ nR)
    (hpz : fmt.pz = piSize p) (hhb : fmt.hb = headerBytesP p) (hocc : fmt.occ = occ)
    (hqc : 32 + (headerBytesP p - 8) ≤ queryCap)
    (hokS : ∀ vk c π, parseOk p vk c π = true → Lvm.ASM.okS vk c (xOfH (headerBytesP p) π) = true)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf p (schedule p)) [] fun _ _ ↦ True)
    (hst : stA p (atomsOf p (schedule p)) 0 [] [] occ = true)
    (hw : WAt fmt.rw 0 (widthsA (atomsOf p (schedule p))))
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VS vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeSW fmt vk PS).V c π).runSeq tr = some true := by
  -- the header check
  rw [hVS] at h
  by_cases hp : parseOk p vk c π = true
  swap
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  simp only [hp, ↓reduceIte] at h
  have hsize : π.size = piSize p := (parseOk_parts hp).1
  have h8 := eight_le_P p
  have hHle : headerBytesP p ≤ π.size := hsize ▸ headerBytesP_le_piSize _
  -- the driver: q₀, the seed, the schedule
  unfold drive at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run _ π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  set hb := headerBytesP p with hbdef
  have hlog : streamOf sf.log = traceBytesB ((q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀ hb, st₀) :: rest with htr
  set x := xOfH hb π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpre : Pre (traceBytesB tr) vk c x := hPre vk c π _ hp (seed_bytesH π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := hD vk c _ hF
  obtain ⟨b, hb1, -, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpre (RS.startH hb) hok0 hacc
  obtain ⟨⟨o, rs', nW⟩, hW⟩ : ∃ r, ivpW capS occ shpS fmt.rw (PS x) (traceBytesB tr) (RS.startH hb) 0 = r :=
    ⟨_, rfl⟩
  rw [hW] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  set S := Lvm.ASM.schemeSW fmt vk PS with hSdef
  have hJ0 : J S π tr ⟨hb, hb, st₀, [(seedQuery π a₀ hb, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop hb) (RS.startH hb) 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_twoH π a₀ st₀ rest h8 hHle).symm,
      by show 0 = hb - hb; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    simW (S := S) (π := π) (tr := tr) (p := p)
      rfl rfl rfl capOfS_eq hocc (atomsOf p (schedule p)) (PS x) [] _ _
      st₀ [] [] _ (RS.startH hb) 2 [] [] _ true rs' 0 nW (hfol x) (by rw [Nat.sub_self]; exact hst) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hbb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hbb
        rw [hbb.1])
      h2 hw hW
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hqc' : 32 + x.length ≤ queryCap := by
    rw [hx, length_xOfH π hHle]; exact hqc
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop hb) := by
    show Lvm.ASM.hdrSW fmt.pz fmt.hb π = _
    rw [hpz, hhb]
    exact hdrSW_of_parseOk hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [show Lvm.ASM.okS vk c x = true from hokS vk c π hp]
    simp [hqc']
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ hb from toQ_seedH π a₀ hb, runSeq_query_eq,
    show S.P x = PS x from rfl, runW_eq_runKW,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

/-- `refines_seqOfGO` at `occS` (P20's occupied words: `fmt.occ = occOfS`). -/
theorem refines_seqOfG (p : Params) (fmt : Lvm.ASM.SFmt) (VS : Lvm.T.SProg)
    (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (prog : RecursionFast.Digest → RecursionFast.Digest → DM Acc) (φ : Acc → Prop)
    (Pre : ByteArray → RecursionFast.Digest → RecursionFast.Digest → List UInt8 → Prop)
    (hVS : ∀ vk c π, VS vk c π = if parseOk p vk c π then drive p π (D vk c) else .ret false)
    (hD : ∀ vk c sig, D vk c sig = true →
      (runD (prog vk c) sig (RS.startH (headerBytesP p))).2.ok = true ∧
        φ (runD (prog vk c) sig (RS.startH (headerBytesP p))).1)
    (hPre : ∀ vk c π sig, parseOk p vk c π = true →
      (∀ t < headerBytesP p - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) →
      Pre sig vk c (xOfH (headerBytesP p) π))
    (href : ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), Pre sig vk c x →
      RefAtPW capS occS shpS fmt.rw sig 0 (prog vk c) (PS x) (fun _ b ↦ b = true) φ nR)
    (hpz : fmt.pz = piSize p) (hhb : fmt.hb = headerBytesP p) (hocc : fmt.occ = Lvm.ASM.occOfS)
    (hqc : 32 + (headerBytesP p - 8) ≤ queryCap)
    (hokS : ∀ vk c π, parseOk p vk c π = true → Lvm.ASM.okS vk c (xOfH (headerBytesP p) π) = true)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf p (schedule p)) [] fun _ _ ↦ True)
    (hst : stA p (atomsOf p (schedule p)) 0 [] [] = true)
    (hw : WAt fmt.rw 0 (widthsA (atomsOf p (schedule p))))
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VS vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeSW fmt vk PS).V c π).runSeq tr = some true :=
  refines_seqOfGO PS nR p fmt VS D prog φ Pre hVS hD hPre href hpz hhb (hocc.trans occOfS_eq) hqc hokS hfol hst hw vk c π tr h

end Main

end Lvm.VEq
