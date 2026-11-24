-- New for lvm6 (WP-V1, part 1): the executable `V_S` front (`Lvm6VDrive`) is the specified compiled
-- verifier (`Lvm6VSpec`, season 1's `Scheme.V`): equality of the two query programs, for every decision
-- whose executable form agrees with its specification on the transcript.
import Lvm6VDrive
import LvmVEqCodec
import LvmReplayBase
import RecursionFast.Library.Oracle

/-!
# `VS6` is the compiled scheme's verifier

**`VS6_eq`**: for every decision `dec` on (header bytes, transcript) and every executable `F` with
`F π acc = dec (HDR of π) (acc read off π)` (`NV.val`: a read is `eOfBytes` of its bytes, an
answer is `chalOf` of it, a leaf offset is the row `padRowOf kOfBytes` of its bytes),
`VS6 sh F vk c π = (scheme6V sh vk dec).V c π` as query programs. So the two agree under every oracle,
every log (`runLog`) and every trace (`runSeq`, `VS6_runSeq`): the compiled `V` is the specified one.

The proof is a simulation (`Sim nf f`: from every driver state, the driver step `nf` and the compiled run
of the specification step `f` are the same program, given the same of their continuations), shown for
each of the seven primitives (`sim_rd`, `sim_draw`, `sim_cap`, `sim_open`, …) and closed under `seq`;
the schedule's expansion is shared (`Prims.walk`), so `sim_walk` is an induction.

* `sim_rd`: the `w` bytes `π[off, off + w)` are `body.take w` (`w` the scheme's width of the read, `WOk`) and the
  absorbed bytes `buf ++ …`.
* `sim_draw`: the query `st ‖ buf` is `toQ (st.toList ++ buf)`; `answerBits a = eToNat (chalOf a)`
  (`Lvm.VEq.answerBits_eq`), so the proof of work and the positions agree.
* `sim_cap`: the cap bytes and the cap record (`Scheme.capI`) of the body at the cap's offset.
* `sim_open`: `climbN` is `Scheme.climb` (`climb_eq`), `openN` is `Scheme.openAll` (`openAll_eq`), and
  `capHit` is the cap lookup `ci.cap[idx]? = some top` (`capHit_iff`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## The transcript read off `π` -/

/-- **A driver entry as a value of the specification's transcript.** -/
def NV.val (π : ByteArray) : NV → Val
  | .rd o w => .e (eOfBytes (((bl π).drop o).take w))
  | .draw a => .c (chalOf a)
  | .cap ht w => .cap ht w
  | .rows i ps wd oc lb os => .rows i ps (os.map fun o => padRowOf kOfBytes wd oc (((bl π).drop o).take lb))

section Sim

variable (sh : VShape) (vk : Digest) (dec : List UInt8 → List Val → Bool) (π : ByteArray)

/-- The cap records of the driver's caps. -/
def capsV (cs : List (Nat × Nat × Nat)) : List CapI :=
  cs.map fun c => (scheme6V sh vk dec).capI c.2.1 c.2.2 ((bl π).drop c.1)

/-- The compiled run of `p` from the driver state `ns` (the read index is the driver's count). -/
def specAt (ns : NS) (p : VerifierProgram Bool) : OProg Bool :=
  (scheme6V sh vk dec).runW ns.nr p ns.st (bl ns.buf) (capsV sh vk dec π ns.caps) ((bl π).drop ns.off)

/-- The scheme's next reads from `ns` have the widths `w`. -/
def WOk (w : List Nat) (ns : NS) : Prop :=
  ∀ j (hj : j < w.length), (scheme6V sh vk dec).rw (ns.nr + j) = w[j]

/-- Two continuations agree on the states whose next reads have the widths `w`. -/
def Hk (w : List Nat) (kN : NS → OProg Bool) (ks : Kt) : Prop :=
  ∀ ns, WOk sh vk dec w ns → kN ns = specAt sh vk dec π ns (ks ns.ps (ns.acc.map (NV.val π)))

/-- **Simulation**: a step whose reads have the widths `wf`; the driver step and the specification step
agree whenever their continuations do. -/
def Sim (wf : List Nat) (nf : NStep) (f : St) : Prop :=
  ∀ w kN ks, Hk sh vk dec π w kN ks → ∀ ns, WOk sh vk dec (wf ++ w) ns →
    nf ns kN = specAt sh vk dec π ns (f ns.ps (ns.acc.map (NV.val π)) ks)

theorem Sim.congr {wf wf' : List Nat} {nf : NStep} {f : St} (h : wf = wf') (hs : Sim sh vk dec π wf nf f) :
    Sim sh vk dec π wf' nf f := h ▸ hs

theorem WOk.same {w : List Nat} {ns ns' : NS} (h : WOk sh vk dec w ns) (hn : ns'.nr = ns.nr) :
    WOk sh vk dec w ns' := fun j hj => by rw [hn]; exact h j hj

theorem WOk.drop {a w : List Nat} {ns ns' : NS} (h : WOk sh vk dec (a ++ w) ns) (hn : ns'.nr = ns.nr + a.length) :
    WOk sh vk dec w ns' := fun j hj => by
  have := h (a.length + j) (by simp; omega)
  rw [hn, Nat.add_assoc, this, List.getElem_append_right (by omega)]
  simp

theorem sim_skip : Sim sh vk dec π [] (PN π sh.levs).skip PS.skip := fun _ _ _ hH ns hw => hH ns hw

theorem sim_seq {wf wg : List Nat} {nf ng : NStep} {f g : St} (hf : Sim sh vk dec π wf nf f)
    (hg : Sim sh vk dec π wg ng g) : Sim sh vk dec π (wf ++ wg) ((PN π sh.levs).seq nf ng) (PS.seq f g) :=
  fun w kN ks hH ns hw =>
    hf (wg ++ w) (fun ns' => ng ns' kN) (fun ps acc => g ps acc ks) (fun ns' hw' => hg w kN ks hH ns' hw') ns
      (by rwa [List.append_assoc] at hw)

theorem sim_reset : Sim sh vk dec π [] (PN π sh.levs).reset PS.reset := fun _ _ _ hH ns hw => hH _ hw

/-! ## Bytes -/

theorem bl_toQ (l : List UInt8) : bl (toQ l) = l := rfl

theorem length_drop_bl (o : Nat) : ((bl π).drop o).length = π.size - o := by
  rw [List.length_drop, ← size_bl]

theorem bl_extract' {o w : Nat} : bl (π.extract o (o + w)) = ((bl π).drop o).take w := by
  rw [bl_extract, Nat.add_sub_cancel_left]

theorem extract_toQ (o w : Nat) : π.extract o (o + w) = toQ (((bl π).drop o).take w) :=
  ba_ext (by rw [bl_extract', bl_toQ])

/-! ## Reads -/

theorem sim_rd (w : Nat) : Sim sh vk dec π [w] ((PN π sh.levs).rd w) (PS.rd w) := by
  intro wr kN ks hH ns hw
  simp only [PN, PS, specAt, Scheme.runW]
  have hrw : (scheme6V sh vk dec).rw ns.nr = w := by simpa using hw 0 (by simp)
  rw [hrw, length_drop_bl]
  by_cases h : π.size - ns.off < w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, hH]
    · simp only [specAt, bl_append, bl_extract', List.drop_drop, List.map_cons, NV.val] <;> rfl
    · exact WOk.drop sh vk dec (a := [w]) hw rfl

/-! ## Draws -/

theorem sim_draw (chk : Nat → Bool) (upd : List Nat → Nat → List Nat) :
    Sim sh vk dec π [] ((PN π sh.levs).draw chk upd) (PS.draw chk upd) := by
  intro wr kN ks hH ns hw
  simp only [PN, PS, specAt, Scheme.runW]
  rw [size_bl]
  by_cases h : 32 + (bl ns.buf).length ≤ queryCap
  · rw [if_pos h, if_pos h]
    have hq : Lvm.digestBytes ns.st ++ ns.buf = toQ (ns.st.toList ++ bl ns.buf) :=
      ba_ext (by rw [bl_append, bl_digestBytes, bl_toQ])
    rw [hq]
    congr 1
    funext a
    have hN : LeanVM.Protocol.Verifier.eToNat ((scheme6V sh vk dec).chal a) = Lvm.answerBits a :=
      (Lvm.VEq.answerBits_eq a).symm
    rw [hN]
    by_cases hc : chk (Lvm.answerBits a) = true
    · simp only [hc, if_true]
      rw [hH] <;> first | rfl | exact WOk.same sh vk dec hw rfl
    · simp only [hc]
      rfl
  · rw [if_neg h, if_neg h]

/-! ## Caps -/

theorem sim_cap (ht w : Nat) : Sim sh vk dec π [] ((PN π sh.levs).cap ht w) (PS.cap ht w) := by
  intro wr kN ks hH ns hw
  simp only [PN, PS, specAt, Scheme.runW]
  have hcb : (scheme6V sh vk dec).capBytes ht w = 32 * 2 ^ capOfL sh.levs ht w := rfl
  rw [hcb, length_drop_bl]
  have hp := Nat.two_pow_pos (capOfL sh.levs ht w)
  by_cases h : π.size < ns.off + 32 * 2 ^ capOfL sh.levs ht w
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), hH]
    · simp only [specAt, bl_append, bl_extract', List.drop_drop, capsV, List.map_append, List.map_cons,
        List.map_nil, NV.val]
    · exact WOk.same sh vk dec hw rfl

/-! ## Openings -/

/-- The cap entry above a position. -/
theorem capHit_iff (co ht w p : Nat) (top : Digest) :
    ((scheme6V sh vk dec).capI ht w ((bl π).drop co)).cap[p % 2 ^ ht / 2 ^ (ht - capOfL sh.levs ht w)]? =
      some top ↔ capHit π co ht (capOfL sh.levs ht w) p top = true := by
  simp only [capHit, Bool.and_eq_true, decide_eq_true_eq]
  have hcap : ((scheme6V sh vk dec).capI ht w ((bl π).drop co)).cap =
      digestsOf (((bl π).drop co).take (32 * 2 ^ capOfL sh.levs ht w)) (2 ^ capOfL sh.levs ht w) := rfl
  rw [hcap, digestsOf]
  generalize capOfL sh.levs ht w = lv
  generalize p % 2 ^ ht / 2 ^ (ht - lv) = idx
  by_cases hi : idx < 2 ^ lv
  · have hd : dg ((((bl π).drop co).take (32 * 2 ^ lv)).drop (32 * idx)) = Lvm.digestAt π (co + 32 * idx) := by
      apply Vector.ext
      intro i hi32
      simp only [dg, Lvm.digestAt, Vector.getElem_ofFn]
      rw [get!_bl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take,
        if_pos (by omega), List.getElem?_drop, Nat.add_assoc]
    rw [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq, hd]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
  · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hi⟩

theorem climb_eq : ∀ (m : Nat) (d : Digest) (q off : Nat) (g : Option (Digest × Bytes) → OProg Bool),
    g none = .ret false →
    (Scheme.climb m d q ((bl π).drop off)).bind g =
      climbN π m d q off fun top off' => g (some (top, (bl π).drop off')) := by
  intro m
  induction m with
  | zero => intro d q off g _; rfl
  | succ m ih =>
    intro d q off g hg
    simp only [Scheme.climb, climbN]
    rw [length_drop_bl]
    by_cases h : π.size < off + 32
    · rw [if_pos (by omega), if_pos h]
      exact hg
    · rw [if_neg (by omega), if_neg h]
      have hq : toQ (if q % 2 = 0 then d.toList ++ ((bl π).drop off).take 32
          else ((bl π).drop off).take 32 ++ d.toList) =
          (if q % 2 = 0 then Lvm.digestBytes d ++ π.extract off (off + 32)
            else π.extract off (off + 32) ++ Lvm.digestBytes d) := by
        apply ba_ext
        split <;> simp only [bl_toQ, bl_append, bl_digestBytes, bl_extract']
      simp only [OProg.bind]
      rw [hq]
      refine congrArg (OProg.query _) (funext fun d' => ?_)
      rw [List.drop_drop]
      exact ih d' (q / 2) (off + 32) g hg

theorem openAll_eq (co ht w : Nat) :
    ∀ (ps : List Nat) (off : Nat) (g : Option (List (List K) × Bytes) → OProg Bool) (kN : Nat → List Nat → OProg Bool),
    g none = .ret false →
    (∀ off' os, kN off' os = g (some (os.map fun o => padRowOf kOfBytes w (occL sh.levs ht w)
        (((bl π).drop o).take (8 * min (occL sh.levs ht w) w)), (bl π).drop off'))) →
    ((scheme6V sh vk dec).openAll ((scheme6V sh vk dec).capI ht w ((bl π).drop co)) ps ((bl π).drop off)).bind g =
      openN π co ht (capOfL sh.levs ht w) (8 * min (occL sh.levs ht w) w) ps off kN := by
  intro ps
  induction ps with
  | nil =>
    intro off g kN _ hk
    show _ = kN off []
    rw [hk]
    rfl
  | cons p ps ih =>
    intro off g kN hg hk
    simp only [Scheme.openAll, openN]
    rw [OProg.bind_assoc]
    simp only [Scheme.openOne]
    have hlb : (scheme6V sh vk dec).lb ((scheme6V sh vk dec).capI ht w ((bl π).drop co)) =
        8 * min (occL sh.levs ht w) w := rfl
    rw [hlb, length_drop_bl]
    by_cases h : π.size - off < 8 * min (occL sh.levs ht w) w
    · rw [if_pos h, if_pos h]
      exact hg
    · rw [if_neg h, if_neg h, ← extract_toQ]
      simp only [OProg.bind]
      refine congrArg (OProg.query _) (funext fun d₀ => ?_)
      rw [OProg.bind_assoc, List.drop_drop]
      have hci : ((scheme6V sh vk dec).capI ht w ((bl π).drop co)).ht = ht := rfl
      have hcl : ((scheme6V sh vk dec).capI ht w ((bl π).drop co)).lv = capOfL sh.levs ht w := rfl
      rw [hci, hcl]
      refine (climb_eq π _ d₀ _ _ _ hg).trans ?_
      refine congrArg (climbN π (ht - capOfL sh.levs ht w) d₀ (p % 2 ^ ht) (off + 8 * min (occL sh.levs ht w) w))
        (funext fun top => funext fun off' => ?_)
      simp only [OProg.bind]
      by_cases hc : capHit π co ht (capOfL sh.levs ht w) p top = true
      · rw [if_pos ((capHit_iff sh vk dec π co ht w p top).mpr hc), if_pos hc]
        simp only
        rw [OProg.bind_assoc]
        refine ih off' _ _ hg ?_
        intro off'' os
        rw [hk]
        rfl
      · rw [if_neg (fun h' => hc ((capHit_iff sh vk dec π co ht w p top).mp h')), if_neg hc]
        exact hg

theorem sim_open (i : Nat) : Sim sh vk dec π [] ((PN π sh.levs).opn i) (PS.opn i) := by
  intro wr kN ks hH ns hw
  simp only [PN, PS, specAt, Scheme.runW, capsV, List.getElem?_map]
  rcases hc : ns.caps[i]? with _ | ⟨co, ht, w⟩
  · rfl
  · simp only [Option.map_some]
    refine (openAll_eq sh vk dec π co ht w ns.ps ns.off _ _ rfl ?_).symm
    intro off' os
    rw [hH] <;> first | rfl | exact WOk.same sh vk dec hw rfl

/-! ## The schedule -/

theorem sim_rep {wf : List Nat} {nf : NStep} {f : St} (hf : Sim sh vk dec π wf nf f) :
    ∀ m, Sim sh vk dec π (List.replicate m wf).flatten ((PN π sh.levs).rep nf m) (PS.rep f m)
  | 0 => sim_skip sh vk dec π
  | m + 1 => sim_seq sh vk dec π hf (sim_rep hf m)

theorem sim_posRest (ht : Nat) :
    ∀ cs, Sim sh vk dec π [] ((PN π sh.levs).posRest ht cs) (PS.posRest ht cs)
  | [] => sim_skip sh vk dec π
  | _ :: cs => sim_seq sh vk dec π (sim_draw sh vk dec π _ _) (sim_posRest ht cs)

theorem sim_item (it : Item) :
    Sim sh vk dec π (widthsI it) ((PN π sh.levs).item sh.levs it) (PS.item sh.levs it) := by
  cases it with
  | E k => exact sim_rep sh vk dec π (sim_rd sh vk dec π 16) _
  | K k => exact sim_rep sh vk dec π (sim_rd sh vk dec π 8) _
  | cap i => exact sim_cap sh vk dec π _ _
  | G g => exact sim_seq sh vk dec π (sim_rd sh vk dec π 8) (sim_draw sh vk dec π _ _)
  | D k => exact Sim.congr sh vk dec π (by simp [widthsI]) (sim_rep sh vk dec π (sim_draw sh vk dec π _ _) k)
  | B => exact sim_draw sh vk dec π _ _
  | pos i g =>
    exact sim_seq sh vk dec π (sim_reset sh vk dec π) (sim_seq sh vk dec π (sim_rd sh vk dec π 8)
      (sim_seq sh vk dec π (sim_draw sh vk dec π _ _) (sim_posRest sh vk dec π _ _)))
  | «open» i => exact sim_open sh vk dec π i

theorem sim_walk : ∀ s, Sim sh vk dec π (widths s) (driveN π sh.levs s) (PS.walk sh.levs s)
  | [] => sim_skip sh vk dec π
  | it :: s => sim_seq sh vk dec π (sim_item sh vk dec π it) (sim_walk s)

end Sim

/-! ## The verifier -/

/-- **The executable `V_S` front is the specified compiled verifier**, for every decision whose
executable form agrees with it on the transcript read off `π`. -/
theorem isEmpty_drop_bl (π : ByteArray) (o : Nat) : ((bl π).drop o).isEmpty = decide (π.size ≤ o) := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.drop_eq_nil_iff, ← size_bl, decide_eq_true_iff]

theorem VS6_eq (sh : VShape) (vk : Digest) (dec : List UInt8 → List Val → Bool) (F : ByteArray → List NV → Bool)
    (hF : ∀ π acc, F π acc = dec ((bl π).take (hdrLen sh)) (acc.map (NV.val π))) (c : Digest) (π : Proof) :
    VS6 sh F vk c π = (scheme6V sh vk dec).V c π := by
  unfold VS6 Scheme.V
  rw [show (scheme6V sh vk dec).hdr π = hdr6 sh π from rfl]
  unfold hdr6
  by_cases h : hdrLen sh ≤ π.size
  · rw [if_pos h, if_pos h]
    dsimp only
    have hx : π.extract 0 (hdrLen sh) = ⟨((bl π).take (hdrLen sh)).toArray⟩ :=
      ba_ext (by rw [bl_extract, List.drop_zero, Nat.sub_zero]; rfl)
    have hlen : ((bl π).take (hdrLen sh)).length = hdrLen sh := by
      rw [List.length_take, ← size_bl]; omega
    have henc : (enc6 ((bl π).take (hdrLen sh))).length = hdrLen sh := hlen
    have hpre : (scheme6V sh vk dec).preOk c (π.data.toList.take (hdrLen sh)) =
        (hdrOkWith leafStmtF nodeStmtF sh.nStar vk c (π.extract 0 (hdrLen sh)) &&
          decide (32 + hdrLen sh ≤ queryCap)) := by
      show (hdrOkWith leafStmt nodeStmt sh.nStar vk c ⟨((bl π).take (hdrLen sh)).toArray⟩ &&
          decide (32 + (enc6 ((bl π).take (hdrLen sh))).length ≤ queryCap)) = _
      rw [henc, leafStmtF_eq, nodeStmtF_eq, hx]
    rw [hpre]
    by_cases hok : (hdrOkWith leafStmtF nodeStmtF sh.nStar vk c (π.extract 0 (hdrLen sh)) &&
        decide (32 + hdrLen sh ≤ queryCap)) = true
    · rw [if_pos hok, if_pos hok]
      refine congrArg (OProg.query q0Q) (funext fun a₀ => ?_)
      have hseed : Lvm.digestBytes a₀ ++ π.extract 0 (hdrLen sh) =
          (scheme6V sh vk dec).seedQ a₀ (π.data.toList.take (hdrLen sh)) := by
        apply ba_ext
        rw [bl_append, bl_digestBytes, hx]
        rfl
      rw [hseed]
      refine congrArg (OProg.query _) (funext fun st => ?_)
      refine sim_walk sh vk dec π sh.sched [] (fun ns => .ret (F π ns.acc && decide (π.size ≤ ns.off)))
        (fun _ acc => .ret (dec ((bl π).take (hdrLen sh)) acc)) ?_ ⟨hdrLen sh, ByteArray.empty, st, [], [], [], 0⟩ ?_
      rotate_left
      · intro j hj
        simp only [List.append_nil] at hj ⊢
        show (widths sh.sched).getD (0 + j) 8 = _
        rw [Nat.zero_add, List.getD_eq_getElem _ _ hj]
      intro ns _
      show OProg.ret (F π ns.acc && decide (π.size ≤ ns.off)) =
        OProg.ret (dec ((bl π).take (hdrLen sh)) (ns.acc.map (NV.val π)) && ((bl π).drop ns.off).isEmpty)
      rw [hF, isEmpty_drop_bl]
    · rw [if_neg hok, if_neg hok]
  · (rw [if_neg h, if_neg h]) <;> rfl

/-- **On every trace** the executable `V_S` front and the specified compiled verifier give the same
verdict (the badge's `runSeq`, `Certificate.lean`'s `acc`). -/
theorem VS6_runSeq (sh : VShape) (vk : Digest) (dec : List UInt8 → List Val → Bool) (F : ByteArray → List NV → Bool)
    (hF : ∀ π acc, F π acc = dec ((bl π).take (hdrLen sh)) (acc.map (NV.val π))) (c : Digest) (π : Proof)
    (tr : Trace) : (VS6 sh F vk c π).runSeq tr = ((scheme6V sh vk dec).V c π).runSeq tr := by
  rw [VS6_eq sh vk dec F hF]

/-- **On every log** (`SSound`'s refinement condition, `LvmCertSGen`): acceptance of the executable
`V_S` front is acceptance of the specified compiled verifier. -/
theorem VS6_refines (sh : VShape) (vk : Digest) (dec : List UInt8 → List Val → Bool) (F : ByteArray → List NV → Bool)
    (hF : ∀ π acc, F π acc = dec ((bl π).take (hdrLen sh)) (acc.map (NV.val π))) (L : Log) (c : Digest)
    (π : Proof) : (VS6 sh F vk c π).runLog L = ((scheme6V sh vk dec).V c π).runLog L := by
  rw [VS6_eq sh vk dec F hF]

end Lvm6.V
