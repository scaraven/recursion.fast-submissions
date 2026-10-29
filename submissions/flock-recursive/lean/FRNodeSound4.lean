-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.3 `node_sound`, §4.4; stage S-N2, residual 3 of
-- `ks_rev4F`). The 3.x analogue is `FRNodeSoundA` (`SlotRest`, `slotHolds_of`).
import FRNodeRows4Fit
import FRVIRTpl4Bridge
import FRVerifierImplNode4F
import FRVIR4Uni

/-!
# The slot interface of the revision 4.1 node circuit (`SlotIface4` at `lRows4`, `nodeIRows4`)

S-E12a's `N4c.SlotIface4` asks, per verifier slot `v` of a node of kind `κ`, for three predicates
(`imp`, `rep`, `tpl`), the kind selectors (`selN`, `selS`), and the soundness of the slot under
them. This module instantiates it at the compiled rows of S-E12b … S-E12f.

* **The rows.** Slot `v`'s rows are its prototype's (`protoOf κ v`: `0` the previous-node group,
  `1` the segment group) moved into region `v` (`slotRows4`). On the slot's assignment
  `slotAsg κ v w` they are the prototype's compiled rows and template rows (`slotIRows_snd`,
  `slotRows_hold`): **`tpl`** (`SlotRows`) is that both hold, and it follows from the node's M rows
  (`tpl_of_rows`).
* **The selectors.** `selN κ v w κ'`: `v` is the previous node's slot and its selector copies pick
  the index `ι` of the node group with `nodeAt ι = κ'`; `selS` likewise for the segment group
  (`segAt`). The copies are linked to L's selector bits and made one-hot by `linkRows4`
  (S-E12c's `selP_sel`, `selA_sel`).
* **`imp`** (`SlotImp`) is *exactly* what `protoCS_soundAt` asks beyond the rows, at every index
  the selectors may pick: the run of the group program at that index on the slot's input and trace
  exists and uses the trace up (`exec … = some (s, [])`), the auxiliary cells hold their registers'
  bits and field elements, every import register's cells hold its value, every foreign flag holds;
  and the statement fact `stmtOk4` that `VsegC`/`VnodeC` check after the run (INT-8). **No row of
  `nodeIRows4` or `lRows4` binds any of these** (the pack map, the replay `R` and the WOTS rows are
  not built): they are the node circuit's soundness gap (`S-N2-RESULT.md`).
* **`rep`** is `True`: the circuit has no replay `R`; the values it would replay are import
  registers, so they sit in `imp`.
* **`soundN`/`soundS`**: `protoCS_soundAt` at the slot's assignment, under the kind-blind ops
  `implP` (the kind's ops read at its table's kind, `OpImpl.fixK`), then INT-8's
  `progNodeGK_exec`/`progSegG_exec` (the group program at index `ι` runs as the kind's program),
  then `runStmt_iff`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The slot's rows -/

theorem map_snd_zipIdx_map {α β : Type*} (l : List α) (f : α × ℕ → ℕ) (g : α → β) :
    (l.zipIdx.map fun p => (f p, g p.1)).map Prod.snd = l.map g := by
  rw [List.map_map]
  show (l.zipIdx.map (g ∘ Prod.fst)) = _
  rw [← List.map_map, List.zipIdx_map_fst 0 l]

/-- An instance's indexed rows are its template rows. -/
theorem tinIRows_snd (L : TLay) (one : Lin) (off : ℕ) (t : Tpl.TKey × ℕ × List Lin) :
    (tinIRows L one off t).map Prod.snd = Tpl.instRows L.ctx one t := by
  have h : (tRows t.1).map (Tpl.instRowA one t.2.2.toArray (L.cb t.1 t.2.1)) = Tpl.instRows L.ctx one t := by
    rw [tRows_eq, show Tpl.instRowA one t.2.2.toArray (L.cb t.1 t.2.1) = Tpl.instRow one t.2.2 (L.cb t.1 t.2.1)
      from funext (Tpl.instRowA_eq one t.2.2 _)]; rfl
  unfold tinIRows
  split <;> rw [map_snd_zipIdx_map, h]

/-- **A slot's indexed rows are its compiled rows, then its template rows.** -/
theorem slotIRows_snd (L : TLay) (one : Lin) (off : ℕ) (cs : CS) :
    (slotIRows L one off cs).map Prod.snd = cs.rowList ++ cs.tplRows L.ctx one := by
  rw [slotIRows, List.map_append, CS.tplRows, List.map_flatMap]
  congr 1
  · exact (map_snd_zipIdx_map cs.rowList (fun p => off + p.2) id).trans (List.map_id _)
  · exact congrArg (List.flatMap · cs.tins) (funext fun t => tinIRows_snd L one off t)

/-- **Slot `v`'s rows**: its prototype's compiled rows and template rows hold at the slot's
assignment. -/
def SlotRows (κ : NodeKind) (v : ℕ) (w : Asg) : Prop :=
  (∀ r ∈ (protoCS (protoOf κ v)).rows, r.Holds (slotAsg κ v w)) ∧
    ∀ r ∈ (protoCS (protoOf κ v)).tplRows (protoLay (protoOf κ v)).ctx (protoP (protoOf κ v)).one,
      r.Holds (slotAsg κ v w)

/-- **The node's M rows give every slot's rows** (when the prototypes fit). -/
theorem slotRows_hold {κ : NodeKind} {v : ℕ} {w : Asg} (hF : ProtoFit) (hv : v < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : SlotRows κ v w := by
  have key : ∀ r ∈ (protoCS (protoOf κ v)).rowList ++
      (protoCS (protoOf κ v)).tplRows (protoLay (protoOf κ v)).ctx (protoP (protoOf κ v)).one,
      r.Holds (slotAsg κ v w) := by
    intro r hr
    rw [← slotIRows_snd] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hm : (mvC (protoOf κ v) v p.1,
        rowMapC (· + κ.oneCell) (rowMapC (mvC (protoOf κ v) v) p.2)) ∈ nodeIRows4 κ := by
      rw [nodeIRows4, if_pos hF]
      refine List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, List.mem_append_left _ ?_⟩
      simp only [slotRows4, absRows4, mvRows, List.map_map]
      exact List.mem_map.2 ⟨p, hp, rfl⟩
    have := hE _ hm
    rw [holds_rowMapC, holds_rowMapC] at this
    exact this
  refine ⟨fun r hr => key r (List.mem_append_left _ ?_), fun r hr => key r (List.mem_append_right _ hr)⟩
  simpa [CS.rowList] using hr

/-- **`tpl` from the statement's rows**: if the prototypes do not fit, the M rows are the rejecting
row `one · one = 0`, which fails at `one = 1`. -/
theorem slotRows_of {κ : NodeKind} {v : ℕ} {w : Asg} (hone : w κ.oneCell = 1) (hv : v < κ.vslots)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) : SlotRows κ v w := by
  by_cases hF : ProtoFit
  · exact slotRows_hold hF hv hE
  · refine absurd (fun p hp => hE p ?_) (rejectRows_ctl κ w hone)
    rw [nodeIRows4, if_neg hF]; exact hp

/-! ## The ops a slot runs under -/

theorem implTF_fixK {F : TFilt} {impl : OpImpl} (h : ImplTF F impl) (κ : Kind) :
    ImplTF F (impl.fixK κ) := fun k hk => by
  have h' := h k hk
  cases k <;> simp only [KeyImpl, OpImpl.fixK] at h' ⊢ <;> first | exact h' | exact fun _ => h' κ | trivial

theorem routeOk_fixK {R : ShR} {impl : OpImpl} {κ : Kind} (h : RouteOk R impl κ) (κ' : Kind) :
    RouteOk R (impl.fixK κ') κ := by
  cases R <;> exact h

theorem implTF_implSeg {impl₀ : OpImpl} (hT : ImplT impl₀) : ImplTF keys41 (implSeg impl₀) :=
  fun k hk => by
    have h := hT.toF keys41 k hk
    cases k
    case shiftMask => exact absurd hk Bool.false_ne_true
    all_goals (simp only [KeyImpl, implSeg] at h ⊢; try first | exact h | exact fun _ => trivial)

/-- **The ops of prototype `π`'s run at index `ι`**: the kind's ops (`implN4F base (nodeAt ι)`, a
node; `implSeg impl₀`, a segment), read at the kind table's kind (`N30` for a node, `L32` for a
segment, the programs' `tix`), so that they do not read the run's index. -/
def implP (impl₀ : OpImpl) (base : NodeKind → OpImpl) (π : ℕ) (ι : Kind) : OpImpl :=
  if π = 0 then (NI4F.implN4F base (nodeAt ι)).fixK .N30 else (implSeg impl₀).fixK .L32

/-- The child kind prototype `π` replays at index `ι`. -/
def kindP (π : ℕ) (ι : Kind) : KindP := if π = 0 then .ofNode (nodeAt ι) else .ofSeg (segAt ι)

theorem nodeOf_eq (ι : Kind) : nodeOf ι = nodeAt ι := by cases ι <;> rfl

theorem implTF_implP {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (π : ℕ) (ι : Kind) : ImplTF (protoF π) (implP impl₀ base π ι) := by
  unfold implP; split_ifs
  · exact implTF_fixK (NI4F.implTF_implN4F hT _) _
  · exact implTF_fixK (implTF_implSeg hT₀) _

theorem routeOk_implP (impl₀ : OpImpl) (base : NodeKind → OpImpl) {π : ℕ} (hπ : π ≤ 1) (ι : Kind) :
    RouteOk (protoR π) (implP impl₀ base π ι) ι := by
  unfold implP; split_ifs with h
  · subst h; exact routeOk_fixK (nodeOf_eq ι ▸ NI4F.routeOk_implN4F base ι) _
  · obtain rfl : π = 1 := by omega
    exact routeOk_fixK (routeOk_implSeg impl₀ ι) _

/-! ## The slot's run (`imp`) -/

/-- **The run-dependent facts of `protoCS_soundAt`** at prototype `π`, index `ι`, ops `impl`: the run
exists and uses the trace up, and the auxiliary, import and foreign facts hold at `w`. -/
def SlotRun (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∃ s : St, exec impl ι inp (protoProg π).ops St.init tr = some (s, []) ∧
    (∀ a ∈ (protoCS π).aux, a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ (protoCS π).imp, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **Slot `v`'s imports** (the instance's `imp`): at every index its selectors may pick, the run
facts (`SlotRun`) at the slot's assignment and the statement fact. -/
def SlotImp (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg) (inp : Input)
    (tr : Trace) : Prop :=
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    SlotRun (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w) ∧
      stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = true

/-- **The selectors**: the previous node's slot picks the node group's index of `κ'`. -/
def SelN (κ : NodeKind) (v : ℕ) (w : Asg) (κ' : NodeKind) : Prop :=
  isPrevSlot κ v = true ∧ ∃ ι, nodeAt ι = κ' ∧ SelOk (slotAsg κ v w) (protoP 0) ι

/-- A segment slot picks the segment group's index of `κ'`. -/
def SelS (κ : NodeKind) (v : ℕ) (w : Asg) (κ' : SegKind) : Prop :=
  isPrevSlot κ v = false ∧ ∃ ι, segAt ι = κ' ∧ SelOk (slotAsg κ v w) (protoP 1) ι

theorem protoOf_prev {κ : NodeKind} {v : ℕ} (h : isPrevSlot κ v = true) : protoOf κ v = 0 := by
  simp [protoOf, h]

theorem protoOf_seg {κ : NodeKind} {v : ℕ} (h : isPrevSlot κ v = false) : protoOf κ v = 1 := by
  simp [protoOf, h]

/-- The node programs' kind table index is `N30`, the segments' `L32`. -/
theorem kindOn_node (κ : NodeKind) (c : List ℕ) (inp : Input) : (progNode κ c).kindOn inp = .N30 := rfl
theorem kindOn_seg (κ : SegKind) (inp : Input) : (progSeg κ).kindOn inp = .L32 := rfl

theorem fixK_fixK (impl : OpImpl) (κ ι : Kind) : (impl.fixK κ).fixK ι = impl.fixK κ := rfl

theorem cells4_len (κ : NodeKind) : (N4c.cells4 κ).length = (N4c.cells4 .N4).length := by
  rw [(N4c.hcells4 κ).1, (N4c.hcells4 .N4).1]

/-- **A slot's soundness at index `ι`**: rows, selectors and the run facts give an accepting run of
the group program at `ι` under `implP`. -/
theorem slot_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) {κ : NodeKind} {v : ℕ} {w : Asg} {ι : Kind} {inp : Input} {tr : Trace}
    (hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) (hR : SlotRows κ v w)
    (hI : SlotRun (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w)) :
    ∃ s : St, exec (implP impl₀ base (protoOf κ v) ι) ι inp (protoProg (protoOf κ v)).ops St.init tr =
      some (s, []) ∧ s.ok = true := by
  obtain ⟨s, he, hx, hi, hf⟩ := hI
  exact ⟨s, he, (protoCS_soundAt (protoOf κ v) (implTF_implP hT₀ hT _ ι)
    (routeOk_implP impl₀ base (protoOf_le' κ v) ι) hS he hR.1 hR.2 hx hi hf).1⟩

/-- **The slot interface at the 4.1 node rows** (`lRows4`, `nodeIRows4`), for bases meeting
`ImplT` (the templates' ops). -/
noncomputable def I4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) :
    N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) where
  lrows := lRows4
  irows := nodeIRows4
  imp κ v w inp tr := SlotImp impl₀ base κ v w inp tr
  rep _ _ _ _ _ := True
  tpl := SlotRows
  selN := SelN
  selS := SelS
  soundN κ v w inp tr κ' _ _ hsel himp _ htpl := by
    obtain ⟨hp, ι, rfl, hS⟩ := hsel
    have h0 := protoOf_prev hp
    replace hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι := by rw [h0]; exact hS
    obtain ⟨hrun, hst⟩ := himp ι hS
    obtain ⟨s, he, hok⟩ := slot_ok hT₀ hT hS htpl hrun
    simp only [h0, implP, kindP, ite_true] at he hst
    rw [show protoProg 0 = progNodeGK N4c.cells4 from rfl,
      progNodeGK_exec N4c.cells4 cells4_len (impl' := NI4F.implN4F base (nodeAt ι)) (κ := .N30)
        (fixK_fixK _ _ _).symm] at he
    obtain ⟨vk, c, π⟩ := inp
    rw [VnodeC, runStmt_iff, runSeq_runIR, semIR, kindOn_node, he]
    exact ⟨by simp [hok], hst⟩
  soundS κ v w inp tr κ' _ _ hsel himp _ htpl := by
    obtain ⟨hp, ι, rfl, hS⟩ := hsel
    have h1 := protoOf_seg hp
    replace hS : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι := by rw [h1]; exact hS
    obtain ⟨hrun, hst⟩ := himp ι hS
    obtain ⟨s, he, hok⟩ := slot_ok hT₀ hT hS htpl hrun
    simp only [h1, implP, kindP, one_ne_zero, if_false] at he hst
    rw [show protoProg 1 = progSegG from rfl,
      progSegG_exec (impl' := implSeg impl₀) (κ := .L32) (fixK_fixK _ _ _).symm] at he
    obtain ⟨vk, c, π⟩ := inp
    rw [VsegC, runStmt_iff, runSeq_runIR, semIR, kindOn_seg, he]
    exact ⟨by simp [hok], hst⟩

theorem I4_rows (impl₀ : OpImpl) (base : NodeKind → OpImpl) (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) :
    (I4 impl₀ base hT₀ hT).lrows = lRows4 ∧ (I4 impl₀ base hT₀ hT).irows = nodeIRows4 := ⟨rfl, rfl⟩

end N4s
end FR
