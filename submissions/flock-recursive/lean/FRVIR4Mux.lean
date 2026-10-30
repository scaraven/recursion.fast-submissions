-- G6: this module also holds the former modules `FRVIR4At` (one section each, in import order).
import FRVIRFinals4
import FRVerifierC4
import FRNodeLayout4

section G6_FRVIR4At

-- New for `flock-recursive` (BLUEPRINT revision 4.3, changes 28, route (A); stage INT-8).

/-!
# A program read at one kind (`Op.at`), and the finals of a group read at one index

Revision 4.3 makes the programs of a group (`{N4, N2, N8}`, `{L32, L30, L31}`) differ in **kind
tables only**: one op list, whose kind-dependent data are tables over the compiler's selector index
(`FRVIR4Mux`). This module gives the reading of such a list at one index and its semantics.

* **`Op.at h pf ι`**: every kind table of an op replaced by its value at `ι` (a constant table);
  `packFK` becomes `packF` if `pf` (the skeleton's segment operand, `FRVIR4.segPtOp`, is a `packF`);
  `hashStmt s` becomes `h s`. `hashStmt` reads the run's kind, not a table, so no reading at `ι` of
  it is exact; `h` is a parameter, and two choices of it that differ on `hashStmt` show that a list
  has none (`noHash_of_at`).
* **`exec_at`**: on a list without `hashStmt`, a run at kind `ι` under `impl` is the run of the list
  read at `ι`, at any kind `κ`, under any `impl'` that reads at `κ` what `impl` reads at `ι`
  (`OpImpl.fixK`: `targetS`, `slotW`, `linkWAll` take the kind; nothing else does).
* **The finals** (`FRVIRFinals4`): `finOps4 P outs b Q` read at `ι` is `finOps4 P outs b (finAt Q ι)`,
  the finals whose per-kind data are `Q ι`'s with its kind tables read at `ι` (`map_at_finOps4`;
  structural, every step definitional). With `Q ι`'s tables constant, `finAt Q ι` is `Q ι` itself;
  with the counts of `P` those of `Q ι` (`finOps4_counts`), the finals are `finOps4 (Q ι)`, the kind's.
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## Reading an op at a kind -/

/-- `hashStmt`. -/
def _root_.FR.Op.isHash : Op → Bool
  | .hashStmt _ => true
  | _ => false

/-- **`op` read at kind `ι`.** -/
def _root_.FR.Op.at (h : Reg → Op) (pf : Bool) (ι : Kind) : Op → Op
  | .const c => .const fun _ => c ι
  | .askNode i hh l r act => .askNode i hh l r fun _ => act ι
  | .idx a b i => .idx (fun _ => a ι) (fun _ => b ι) (fun _ => i ι)
  | .shrN n s => .shrN n fun _ => s ι
  | .packFK xs => if pf then .packF (xs ι) else .packFK fun _ => xs ι
  | .rsWeight r ps k β act ρ => .rsWeight r (fun _ => ps ι) k β (fun _ => act ι) ρ
  | .keep act n o => .keep (fun _ => act ι) n o
  | .hashStmt s => h s
  | .assertEq a b act => .assertEq a b fun _ => act ι
  | .assertBit a act => .assertBit a fun _ => act ι
  | .assertZero a act => .assertZero a fun _ => act ι
  | op => op

/-- The `h` that keeps `hashStmt`, and one that does not (one register each). -/
abbrev hKeep : Reg → Op := .hashStmt
abbrev hDrop : Reg → Op := fun _ => .input 0

theorem outs_at {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (pf : Bool) (ι : Kind) (op : Op) :
    (Op.at h pf ι op).outs = op.outs := by
  cases op <;> first | rfl | exact hh _ | (simp only [Op.at]; split <;> rfl)

theorem opsOut_map_at {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (pf : Bool) (ι : Kind) (ops : List Op) :
    opsOut (ops.map (Op.at h pf ι)) = opsOut ops := by
  simp only [opsOut, List.map_map, Function.comp_def, outs_at hh]

/-- **Two readings that differ on `hashStmt` agree on a list only if it has none.** -/
theorem noHash_of_at {pf : Bool} {ι : Kind} {ops : List Op}
    (h : ops.map (Op.at hKeep pf ι) = ops.map (Op.at hDrop pf ι)) : ∀ op ∈ ops, op.isHash = false := by
  intro op hop
  have := (List.map_inj_left.mp h) op hop
  cases op <;> first | rfl | simp [Op.at] at this

/-- **The relocation commutes with the reading.** -/
theorem reloc_at {h : Reg → Op} (pf : Bool) (ι : Kind) (S : Seq) (hr : ∀ s, reloc S (h s) = h s) (op : Op) :
    Op.at h pf ι (reloc S op) = reloc S (Op.at h pf ι op) := by
  cases op with
  | piField f o len => change _ = reloc S (.piField f o len); simp only [reloc]; split <;> rfl
  | piElem f o => change _ = reloc S (.piElem f o); simp only [reloc]; split <;> rfl
  | piElemK f o => change _ = reloc S (.piElemK f o); simp only [reloc]; split <;> rfl
  | piDigest f o => change _ = reloc S (.piDigest f o); simp only [reloc]; split <;> rfl
  | piDigestAt f o k => change _ = reloc S (.piDigestAt f o k); simp only [reloc]; split <;> rfl
  | packFK xs => cases pf <;> rfl
  | hashStmt s => exact (hr s).symm
  | _ => rfl

theorem reloc_hKeep (S : Seq) (s : Reg) : reloc S (hKeep s) = hKeep s := rfl
theorem reloc_hDrop (S : Seq) (s : Reg) : reloc S (hDrop s) = hDrop s := rfl

/-! ## The semantics of the reading -/

/-- `impl` with its kind-reading ops read at `ι`. -/
def _root_.FR.OpImpl.fixK (impl : OpImpl) (ι : Kind) : OpImpl :=
  { impl with
    targetS := fun _ => impl.targetS ι
    slotW := fun _ => impl.slotW ι
    linkWAll := fun _ => impl.linkWAll ι }

/-- **An op at kind `ι` under `impl` is the op read at `ι`, at kind `κ`, under `impl'`**, when `impl'`
reads at `κ` what `impl` reads at `ι` (and `op` is not `hashStmt`). -/
theorem evalOp_at {impl impl' : OpImpl} {ι κ : Kind} (hI : impl'.fixK κ = impl.fixK ι) (h : Reg → Op)
    (pf : Bool) (inp : Input) (regs : Array Val) (op : Op) (hop : op.isHash = false) :
    evalOp impl ι inp regs op = evalOp impl' κ inp regs (Op.at h pf ι op) := by
  have e : ∀ {α : Type} (f : OpImpl → α), f (impl'.fixK κ) = f (impl.fixK ι) := fun f => congrArg f hI
  have hl := e OpImpl.lagrangeS; have hz := e OpImpl.eqZ; have hw := e OpImpl.tensorW
  have hr := e OpImpl.rsWeight; have hp := e OpImpl.phiRS; have ha := e OpImpl.walkAB
  have hk := e OpImpl.kindInd; have hm := e OpImpl.evalM; have hL := e OpImpl.evalL
  have hst := e OpImpl.shiftTarget; have hf := e OpImpl.kindFoldWeight; have hsm := e OpImpl.shiftMask
  have hrw := e OpImpl.rowW; have hse := e OpImpl.shiftEq
  have ht := congrFun (e OpImpl.targetS) κ; have hs := congrFun (e OpImpl.slotW) κ
  have hla := congrFun (e OpImpl.linkWAll) κ
  simp only [OpImpl.fixK] at hl hz hw hr hp ha hk hm hL hst hf hsm hrw hse ht hs hla
  cases op with
  | hashStmt s => simp [Op.isHash] at hop
  | packFK xs => simp only [Op.at]; split <;> rfl
  | targetS r => simp only [Op.at, evalOp, ht]
  | slotW s a r => simp only [Op.at, evalOp, hs]
  | linkWAll a r => simp only [Op.at, evalOp, hla]
  | lagrangeS v l pe => simp only [Op.at, evalOp, hl]
  | eqZ a b => simp only [Op.at, evalOp, hz]
  | tensorW j r => simp only [Op.at, evalOp, hw]
  | rsWeight r ps k β act ρ => simp only [Op.at, evalOp, hr]
  | phiRS r a => simp only [Op.at, evalOp, hp]
  | walkAB a b => simp only [Op.at, evalOp, ha]
  | kindInd r => simp only [Op.at, evalOp, hk]
  | evalM a b => simp only [Op.at, evalOp, hm]
  | evalL a b => simp only [Op.at, evalOp, hL]
  | shiftTarget a b c d => simp only [Op.at, evalOp, hst]
  | kindFoldWeight a b c => simp only [Op.at, evalOp, hf]
  | shiftMask a b => simp only [Op.at, evalOp, hsm]
  | rowW a b => simp only [Op.at, evalOp, hrw]
  | shiftEq a b => simp only [Op.at, evalOp, hse]
  | _ => rfl

/-- **Runs of two lists related op by op.** -/
theorem exec_forall₂ {impl impl' : OpImpl} {ι κ : Kind} {inp : Input} {R : Op → Op → Prop}
    (hR : ∀ op op', R op op' → ∀ regs, evalOp impl ι inp regs op = evalOp impl' κ inp regs op') :
    ∀ {ops ops' : List Op}, List.Forall₂ R ops ops' → ∀ (s : St) (tr : Trace),
      exec impl ι inp ops s tr = exec impl' κ inp ops' s tr
  | [], [], .nil, _, _ => rfl
  | op :: ops, op' :: ops', .cons hr hrs, s, tr => by
    simp only [exec, ← hR op op' hr s.regs]
    rcases evalOp impl ι inp s.regs op with ⟨vs, ok⟩ | q
    · exact exec_forall₂ hR hrs _ _
    · rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · rfl
      · simp only [exec_forall₂ hR hrs]

/-- The relation of an op and its reading at `ι` (`hashStmt` excluded). -/
def AtRel (h : Reg → Op) (pf : Bool) (ι : Kind) (op op' : Op) : Prop :=
  op.isHash = false ∧ op' = Op.at h pf ι op

theorem forall₂_at {h : Reg → Op} {pf : Bool} {ι : Kind} :
    ∀ {ops : List Op}, (∀ op ∈ ops, op.isHash = false) → List.Forall₂ (AtRel h pf ι) ops (ops.map (Op.at h pf ι))
  | [], _ => .nil
  | op :: _, hn => .cons ⟨hn op (List.mem_cons_self ..), rfl⟩
      (forall₂_at fun o ho => hn o (List.mem_cons_of_mem _ ho))

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {a b : List α} {a' b' : List β}, List.Forall₂ R a a' → List.Forall₂ R b b' → List.Forall₂ R (a ++ b) (a' ++ b')
  | [], _, [], _, .nil, hb => hb
  | _ :: _, _, _ :: _, _, .cons h ha, hb => .cons h (forall₂_append ha hb)

/-- **`exec_at`**: a list without `hashStmt`, run at `ι` under `impl`, is its reading at `ι` run at `κ`
under `impl'`. -/
theorem exec_at {impl impl' : OpImpl} {ι κ : Kind} (hI : impl'.fixK κ = impl.fixK ι) (h : Reg → Op)
    (pf : Bool) (inp : Input) (ops : List Op) (hn : ∀ op ∈ ops, op.isHash = false) (s : St) (tr : Trace) :
    exec impl ι inp ops s tr = exec impl' κ inp (ops.map (Op.at h pf ι)) s tr :=
  exec_forall₂ (fun op op' hr regs => by rw [hr.2]; exact evalOp_at hI h pf inp regs op hr.1)
    (forall₂_at hn) s tr

/-! ## Generators without kind tables read at `ι` -/

section Gen
variable (h : Reg → Op) (pf : Bool) (ι : Kind)

theorem map_at_dotOps (x y z c : ℕ) : ∀ n, (dotOps x y z c n).map (Op.at h pf ι) = dotOps x y z c n
  | 0 => rfl
  | n + 1 => by rw [dotOps, List.map_append, map_at_dotOps x y z c n]; rfl

theorem map_at_pinOps : pinOps.map (Op.at h pf ι) = pinOps := by
  rw [pinOps, List.map_map]; rfl

theorem map_at_hornerOps (β b : ℕ) : (hornerOps β b).map (Op.at h pf ι) = hornerOps β b := by
  rw [hornerOps, List.map_flatMap]; rfl

theorem map_at_linkOps (ks b : ℕ) : (linkOps ks b).map (Op.at h pf ι) = linkOps ks b := by
  rw [linkOps, List.map_flatMap]; rfl

theorem map_at_elemsOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, Op.at h pf ι (wop i) = wop i) (R : Reg) :
    ∀ n i aA aT b, (elemsOps j wop R n i aA aT b).map (Op.at h pf ι) = elemsOps j wop R n i aA aT b
  | 0, _, _, _, _ => rfl
  | n + 1, i, aA, aT, b => by
    rw [elemsOps, List.map_append, map_at_elemsOps j wop hw R n]
    simp only [elemOps, List.map_cons, List.map_nil, hw]; rfl

theorem map_at_claimOps_getF (j : ℕ) (a R b : ℕ) :
    (claimOps j (fun i => .getF a i) R b).map (Op.at h pf ι) = claimOps j (fun i => .getF a i) R b := by
  rw [claimOps, List.map_cons, map_at_elemsOps h pf ι j _ (fun _ => rfl)]; rfl

theorem map_at_claimOps_bb (j : ℕ) (R b : ℕ) :
    (claimOps j (fun i => .const fun _ => .f (bb i)) R b).map (Op.at h pf ι) =
      claimOps j (fun i => .const fun _ => .f (bb i)) R b := by
  rw [claimOps, List.map_cons, map_at_elemsOps h pf ι j _ (fun _ => rfl)]; rfl

theorem map_at_accOps (e : Reg) : ∀ ys q acc b, (accOps e ys q acc b).map (Op.at h pf ι) = accOps e ys q acc b
  | [], _, _, _ => rfl
  | y :: ys, q, acc, b => by rw [accOps, List.map_append, map_at_accOps e ys]; rfl

theorem map_at_layerOps (w : Reg) (xs : List Reg) (n b : ℕ) :
    ∀ k, (layerOps w xs n b k).map (Op.at h pf ι) = layerOps w xs n b k
  | 0 => rfl
  | k + 1 => by rw [layerOps, List.map_append, map_at_layerOps w xs n b k]; rfl

theorem map_at_hornerKOps (ws : List Reg) : ∀ v xs b, (hornerKOps ws v xs b).map (Op.at h pf ι) = hornerKOps ws v xs b
  | 0, _, _ => rfl
  | v + 1, xs, b => by rw [hornerKOps, List.map_append, map_at_layerOps, map_at_hornerKOps ws v]

theorem map_at_gEncOps (p : ℕ) (units fin : List Reg) (j y b : ℕ) :
    (gEncOps p units fin j y b).map (Op.at h pf ι) = gEncOps p units fin j y b := by
  rw [gEncOps, List.map_append, List.map_append, map_at_hornerKOps, List.map_map]; rfl

theorem map_at_prodKOps : ∀ xs acc b, (prodKOps xs acc b).map (Op.at h pf ι) = prodKOps xs acc b
  | [], _, _ => rfl
  | x :: xs, acc, b => by rw [prodKOps, List.map_cons, map_at_prodKOps xs]; rfl

theorem map_at_ptsOps (one z0 : Reg) : ∀ ss b, (ptsOps one z0 ss b).map (Op.at h pf ι) = ptsOps one z0 ss b
  | [], _ => rfl
  | s :: ss, b => by
    rw [ptsOps, List.map_append, map_at_ptsOps one z0 ss, ptOps, List.map_append, List.map_map]
    congr 2
    · exact List.map_congr_left fun x _ => by cases x <;> rfl

theorem map_at_gLvsOps (S : Seq) (fi : FinIn) (one cu Ts : Reg) :
    ∀ ks W b, (gLvsOps S fi one cu Ts ks W b).map (Op.at h pf ι) = gLvsOps S fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, List.map_append, map_at_gLvsOps S fi one cu Ts ks, gLvOps]
    simp only [List.map_append, map_at_accOps, List.map_map]; rfl

theorem map_at_fhOps (E : Reg) : ∀ cs acc b, (fhOps E cs acc b).map (Op.at h pf ι) = fhOps E cs acc b
  | [], _, _ => rfl
  | c :: cs, acc, b => by rw [fhOps, List.map_append, map_at_fhOps E cs]; rfl

theorem map_at_padsOps (one : Reg) (sf : List Reg) (p : ℕ) :
    ∀ ms pd, (padsOps one sf p ms pd).map (Op.at h pf ι) = padsOps one sf p ms pd
  | [], _ => rfl
  | m :: ms, pd => by
    rw [padsOps, List.map_append, map_at_padsOps one sf p ms, padOps, List.map_append, map_at_prodKOps,
      List.map_map]; rfl

theorem map_at_selOps (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n pb : ℕ) :
    (selOps sel cand n pb).map (Op.at h pf ι) = selOps (fun i _ => sel i ι) cand n pb := by
  rw [selOps, selOps, List.map_map]; rfl

theorem map_at_gCellsOpsK (nc : ℕ) (one g hh kp : Reg) (cells : ℕ → KC ℕ) :
    ∀ n j acc pw b, (gCellsOpsK nc one g hh kp cells n j acc pw b).map (Op.at h pf ι) =
      gCellsOpsK nc one g hh kp (fun j _ => cells j ι) n j acc pw b
  | 0, _, _, _, _ => rfl
  | n + 1, j, acc, pw, b => by
    rw [gCellsOpsK, gCellsOpsK, List.map_append, map_at_gCellsOpsK nc one g hh kp cells n, gCellOpsK,
      gCellOpsK]
    simp only [List.map_append, map_at_prodKOps, List.map_map]; rfl

end Gen

/-! ## The finals read at an index -/

/-- `P` with its kind tables read at `ι` (constant tables). -/
def FinP.fixKV (P : FinP) (ι : Kind) : FinP :=
  { P with kv := ⟨fun _ => P.kv.m ι, fun _ => P.kv.node ι, fun _ => P.kv.selA ι, fun _ => P.kv.ptIx ι,
    fun _ => P.kv.fsel ι⟩ }

/-- **The per-kind data of index `ι`**, its kind tables read at `ι`, for every index. -/
def finAt (Q : Kind → FinP) (ι : Kind) : Kind → FinP := fun _ => (Q ι).fixKV ι

section Fields
variable (h : Reg → Op) (ι : Kind) (P : FinP) (Q : Kind → FinP) (fi : FinIn) (b : ℕ)

theorem map_at_gFinZ : (gFinZ P fi b Q).1.map (Op.at h false ι) = (gFinZ P fi b (finAt Q ι)).1 := by
  simp only [gFinZ, List.map_append, map_at_pinOps]
  rfl

theorem map_at_gFinLc : (gFinLc P fi b Q).1.map (Op.at h false ι) = (gFinLc P fi b (finAt Q ι)).1 := by
  simp only [gFinLc, gLcHead, List.map_append, map_at_dotOps, map_at_hornerOps, List.map_map]
  rfl

theorem map_at_gFinSh : (gFinSh P fi b Q).1.map (Op.at h false ι) = (gFinSh P fi b (finAt Q ι)).1 := by
  cases hv : P.vn <;> simp only [gFinSh, gShCore, gBndOps, hv, Bool.cond_true, Bool.cond_false, List.map_append,
    List.map_cons, map_at_linkOps] <;> rfl

theorem map_at_gFinLr (hck : P.ck = true) :
    (gFinLr P fi b Q).1.map (Op.at h false ι) = (gFinLr P fi b (finAt Q ι)).1 := by
  simp only [gFinLr, hck, Bool.cond_true]
  rfl

theorem map_at_gFinRS : (gFinRS P fi b Q).1.map (Op.at h false ι) = (gFinRS P fi b (finAt Q ι)).1 := by
  simp only [gFinRS, List.map_append, map_at_claimOps_getF, map_at_claimOps_bb]
  rfl

theorem map_at_gFinE (hck : P.ck = true) :
    (gFinE P fi b Q).1.map (Op.at h false ι) = (gFinE P fi b (finAt Q ι)).1 := by
  cases hr : P.rsvOps <;>
    simp only [gFinE, gFinE0, rsvEOps, rsvSOps, hr, hck, Bool.cond_true, Bool.cond_false, List.map_append,
      List.map_cons, List.map_nil, List.map_map] <;> rfl

theorem gFinE_ex (Q' : Kind → FinP) : (gFinE P fi b Q).2 = (gFinE P fi b Q').2 := by
  unfold gFinE; cases P.rsvOps <;> rfl

theorem map_at_gFinB' : (gFinB' P fi b Q).1.map (Op.at h false ι) = (gFinB' P fi b (finAt Q ι)).1 := by
  cases hr : P.rsvOps <;>
    simp only [gFinB', rsvBOps, hr, Bool.cond_true, Bool.cond_false, List.map_append, List.map_cons,
      List.map_nil, List.map_flatMap, List.map_map] <;> rfl

theorem map_at_gFinP (i : ℕ) : (gFinP P i fi b).1.map (Op.at h false ι) = (gFinP P i fi b).1 := by
  unfold gFinP
  split_ifs
  · simp only [finPLow, List.map_append, map_at_accOps]; rfl
  · simp only [gFinPTop, List.map_append, List.map_flatMap, map_at_gEncOps, List.map_map]; rfl

theorem map_at_gTailOps (p : ℕ) :
    ∀ ts r, (gTailOps Q p ts r).map (Op.at h false ι) = gTailOps (finAt Q ι) p ts r
  | [], _ => rfl
  | t :: ts, r => by rw [gTailOps, gTailOps, List.map_append, map_at_gTailOps p ts]; rfl

theorem map_at_gFinPf (hck : P.ck = true) :
    (gFinPf P fi b Q).1.map (Op.at h false ι) = (gFinPf P fi b (finAt Q ι)).1 := by
  cases hr : P.rsvOps <;>
  simp only [gFinPf, hck, hr, Bool.cond_true, Bool.cond_false, List.map_append, List.map_cons,
    List.map_nil, map_at_ptsOps, List.map_flatMap, map_at_selOps, map_at_gCellsOpsK, map_at_gLvsOps,
    map_at_fhOps, map_at_padsOps, map_at_gTailOps, List.map_map, List.append_nil] <;> rfl

theorem gFinSh_ex (Q' : Kind → FinP) : (gFinSh P fi b Q).2 = (gFinSh P fi b Q').2 := by
  unfold gFinSh; cases P.vn <;> rfl

end Fields

section Cap
variable (h : Reg → Op) (pf : Bool) (ι : Kind)

/-- **The cap check reads no kind table** (revision 4.4.1). -/
theorem map_at_capChkOps (S : Seq) (outs : Array (List Reg)) (b : ℕ) :
    (capChkOps S outs b).map (Op.at h pf ι) = capChkOps S outs b := by
  unfold capChkOps
  split
  · simp only [List.map_append, List.map_flatMap, List.map_map, powChainOps, bitPowOps, macDOps,
      macAOps, List.map_cons, List.map_nil]
    rfl
  · rfl

end Cap

/-- One step of `Finals.ops`' fold. -/
def finStep (outs : Array (List Reg)) (zh : List Reg) (acc : List Op × ℕ × Array (List Reg)) (f : FinField) :
    List Op × ℕ × Array (List Reg) :=
  let x := f ⟨outs, zh, acc.2.2⟩ acc.2.1
  (acc.1 ++ x.1, acc.2.1 + opsOut x.1, acc.2.2.push x.2)

theorem Finals.ops_eq (F : Finals) (outs : Array (List Reg)) (b : ℕ) :
    F.ops outs b = (F.finRS ⟨outs, [], #[]⟩ b).1 ++
      (F.rest.foldl (finStep outs (F.finRS ⟨outs, [], #[]⟩ b).2) ([], b + opsOut (F.finRS ⟨outs, [], #[]⟩ b).1,
        #[(F.finRS ⟨outs, [], #[]⟩ b).2])).1 := rfl

/-- Two fields related by a reading of their ops (`f`), with the same exports. -/
def FMap (f : Op → Op) (g g' : FinField) : Prop := ∀ fi b, (g fi b).1.map f = (g' fi b).1 ∧ (g fi b).2 = (g' fi b).2

theorem foldl_finStep {f : Op → Op} (hf : ∀ op, (f op).outs = op.outs) (outs : Array (List Reg)) (zh : List Reg) :
    ∀ {fs fs' : List FinField}, List.Forall₂ (FMap f) fs fs' → ∀ (ops : List Op) (n : ℕ) (ex : Array (List Reg)),
      fs'.foldl (finStep outs zh) (ops.map f, n, ex) =
        ((fs.foldl (finStep outs zh) (ops, n, ex)).1.map f, (fs.foldl (finStep outs zh) (ops, n, ex)).2)
  | [], [], .nil, _, _, _ => rfl
  | g :: gs, g' :: gs', .cons hg hgs, ops, n, ex => by
    simp only [List.foldl_cons, finStep]
    obtain ⟨h1, h2⟩ := hg ⟨outs, zh, ex⟩ n
    rw [← h1, ← h2, ← List.map_append]
    have ho : opsOut ((g ⟨outs, zh, ex⟩ n).1.map f) = opsOut (g ⟨outs, zh, ex⟩ n).1 := by
      simp only [opsOut, List.map_map, Function.comp_def, hf]
    rw [ho]
    exact foldl_finStep hf outs zh hgs _ _ _

/-- **`Finals.ops` read op by op**, from fields related by the reading. -/
theorem Finals.ops_map {f : Op → Op} (hf : ∀ op, (f op).outs = op.outs) {F F' : Finals}
    (hRS : FMap f F.finRS F'.finRS) (hrest : List.Forall₂ (FMap f) F.rest F'.rest) (outs : Array (List Reg))
    (b : ℕ) : (F.ops outs b).map f = F'.ops outs b := by
  rw [Finals.ops_eq, Finals.ops_eq]
  obtain ⟨h1, h2⟩ := hRS ⟨outs, [], #[]⟩ b
  have ho : opsOut (F'.finRS ⟨outs, [], #[]⟩ b).1 = opsOut (F.finRS ⟨outs, [], #[]⟩ b).1 := by
    rw [← h1]; simp only [opsOut, List.map_map, Function.comp_def, hf]
  rw [List.map_append, h1, ← h2, ho]
  have := foldl_finStep hf outs (F.finRS ⟨outs, [], #[]⟩ b).2 hrest [] (b + opsOut (F.finRS ⟨outs, [], #[]⟩ b).1)
    #[(F.finRS ⟨outs, [], #[]⟩ b).2]
  rw [List.map_nil] at this
  rw [this]

theorem forall₂_self {R : FinField → FinField → Prop} : ∀ {l : List FinField}, (∀ x ∈ l, R x x) → List.Forall₂ R l l
  | [], _ => .nil
  | x :: _, h => .cons (h x (List.mem_cons_self ..)) (forall₂_self fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **The finals of a group read at `ι`** (`ck`: the 4.x programs). -/
theorem map_at_finOps4 {h : Reg → Op} (hh : ∀ s, (h s).outs = 1) (ι : Kind) (P : FinP) (Q : Kind → FinP)
    (hck : P.ck = true) (hr : ∀ s, reloc P.S (h s) = h s) (outs : Array (List Reg)) (b : ℕ) :
    (finOps4 P outs b Q).map (Op.at h false ι) = finOps4 P outs b (finAt Q ι) := by
  simp only [finOps4_def, List.map_map]
  have e : (Op.at h false ι ∘ reloc P.S) = (reloc P.S ∘ Op.at h false ι) :=
    funext (reloc_at false ι P.S hr)
  rw [e, ← List.map_map]
  refine congrArg (List.map (reloc P.S)) ?_
  suffices hF : ((finalsOf P Q).ops outs b).map (Op.at h false ι) = (finalsOf P (finAt Q ι)).ops outs b by
    rw [List.map_append, hF, map_at_capChkOps, ← hF, opsOut_map_at hh]
  have hrest : List.Forall₂ (FMap (Op.at h false ι)) (finalsOf P Q).rest (finalsOf P (finAt Q ι)).rest := by
    simp only [Finals.rest, finalsOf]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ ?_)))))
    · exact fun fi b => ⟨map_at_gFinZ h ι P Q fi b, rfl⟩
    · exact fun fi b => ⟨map_at_gFinLc h ι P Q fi b, rfl⟩
    · exact fun fi b => ⟨map_at_gFinSh h ι P Q fi b, gFinSh_ex P Q fi b _⟩
    · exact fun fi b => ⟨map_at_gFinLr h ι P Q fi b hck, rfl⟩
    · exact fun fi b => ⟨map_at_gFinE h ι P Q fi b hck, gFinE_ex P Q fi b _⟩
    · exact fun fi b => ⟨map_at_gFinB' h ι P Q fi b, rfl⟩
    · apply forall₂_append
      · refine forall₂_self fun g hg => ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
        exact fun fi b => ⟨map_at_gFinP h ι P fi b i, rfl⟩
      · exact .cons (fun fi b => ⟨map_at_gFinPf h ι P Q fi b hck, rfl⟩) .nil
  exact Finals.ops_map (F := finalsOf P Q) (F' := finalsOf P (finAt Q ι)) (outs_at hh false ι)
    (fun fi b => ⟨map_at_gFinRS h ι P Q fi b, rfl⟩) hrest outs b

/-- **`P` and `P'` have the same counts** (the finals' ops and registers depend on these only). -/
def SameCounts (P P' : FinP) : Prop :=
  P.S = P'.S ∧ P.fams = P'.fams ∧ P.e4s = P'.e4s ∧ P.nc = P'.nc ∧ P.vn = P'.vn ∧ P.ck = P'.ck ∧
    P.ncell = P'.ncell ∧ P.tails = P'.tails ∧ P.rsvOps = P'.rsvOps ∧ P.nrcell = P'.nrcell

/-- **The finals read only `P`'s counts.** -/
theorem finOps4_counts {P P' : FinP} (hc : SameCounts P P') (Q : Kind → FinP) (outs : Array (List Reg))
    (b : ℕ) : finOps4 P outs b Q = finOps4 P' outs b Q := by
  obtain ⟨hS, hf, he, hn, hv, hk, hl, ht, hr, hrc⟩ := hc
  have hT : gFinPTop P = gFinPTop P' := by funext fi b; simp only [gFinPTop, hS]
  have hP : gFinP P = gFinP P' := by funext i; simp only [gFinP, hT]
  simp only [finOps4, finalsOf, gFinRS, gRsTail, gFinZ, gFinLc, gLcHead, gFinSh, gShCore, gBndOps, gPadB,
    gFinLr, gFinE, gFinE0, rsvEOps, rsvSOps, gFinB', hP, gFinPf, gPfPts, pfCand, pfCandA, hS, hf, he, hn, hv, hk, hl, ht,
    hr, hrc]

/-- **A kind's own tables, read at any index, are its tables** (constant tables). -/
theorem fixKV_const (P : FinP) (ι : Kind) (hm : ∀ κ, P.kv.m κ = P.kv.m ι) (hn : ∀ κ, P.kv.node κ = P.kv.node ι)
    (hs : ∀ κ, P.kv.selA κ = P.kv.selA ι) (hp : ∀ κ, P.kv.ptIx κ = P.kv.ptIx ι)
    (hf : ∀ κ, P.kv.fsel κ = P.kv.fsel ι) : P.fixKV ι = P := by
  obtain ⟨S, ⟨m, n, s, p, f⟩, rest⟩ := P
  simp only at hm hn hs hp hf
  simp only [FinP.fixKV, FinP.mk.injEq, KV.mk.injEq, true_and, and_true]
  exact ⟨funext fun κ => (hm κ).symm, funext fun κ => (hn κ).symm, funext fun κ => (hs κ).symm,
    funext fun κ => (hp κ).symm, funext fun κ => (hf κ).symm⟩

end Rev4
end FR

end G6_FRVIR4At

section G6_FRVIR4Mux

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3 "The mux", changes 26; stage S-E12b,
-- track L-circ).

/-!
# Revision 4.1's slot programs: the group mux `gen4G` (revision 4.3: uniform groups)

A 4.1 node replays `1 + k` children (B-13): the previous step's node, muxed over `{N2, N4, N8}`,
and `k` segment sub-slots, each muxed over `{L30, L31, L32}` (changes 26, item 5). Each group has
three kinds, so the compiler's three-way selector (`Circ.Params.sel : Kind → Lin`, `muxP`) serves it
unchanged: a **group** `G : Kind → KindP` names the kind each selector index stands for
(`nodeGrp`, `segGrp`), and `gen4G S G fin` is `FRVIR4.gen4` with every kind-dependent datum a table
over the index (`fun ι => … (G ι) …`) instead of a constant.

**Revision 4.3 (route (A)).** The kinds of a group now differ in kind tables only (`FRVIRFinals4`:
the finals read the counts from one `FinP` and the per-kind data of index `ι` from `Q ι`; the final
tail and `hashStmt` are uniform, `FRVIR4`). The group programs are

* `progNodeGK cells = gen4G seq4 nodeGrp (finals of nodeQ cells)`, `nodeQ cells ι` the finals'
  parameters of `nodeAt ι` with its cells `cells (nodeAt ι)`;
* `progSegG = gen4G seq4 segGrp (finals of segQ)`.

**The group program read at `ι` is `gen4 (G ι)`** (`FRVIR4Uni`): op for op (`Op.at`), and so its
run at `ι` is the kind's program's run (`progNodeGK_exec`, `progSegG_exec`).
-/

namespace FR
namespace Rev4
open RecursionFast

/-- **A slot group**: the kind each of the compiler's three selector indices stands for. -/
abbrev Grp := Kind → KindP

/-- The node kind at each selector index (`N4`, `N2`, `N8` at `L32`, `P30`, `N30`). -/
def nodeAt : Kind → NodeKind
  | .L32 => .N4
  | .P30 => .N2
  | .N30 => .N8

/-- The segment kind at each selector index (`L32`, `L30`, `L31` at `L32`, `P30`, `N30`). -/
def segAt : Kind → SegKind
  | .L32 => .L32
  | .P30 => .L30
  | .N30 => .L31

/-- **The previous-node group** `{N4, N2, N8}` at indices `L32, P30, N30`. -/
def nodeGrp : Grp := fun ι => .ofNode (nodeAt ι)

/-- **The segment group** `{L32, L30, L31}` at indices `L32, P30, N30`. -/
def segGrp : Grp := fun ι => .ofSeg (segAt ι)

/-- **A kind table, evaluated once** (its three values computed before the closure is built, so that
an op's table costs a `match`, not a recomputation; `kt_eq`). -/
-- `noinline` (INIT): inlined, the compiler floats each `let` into its `match` branch, so every
-- application recomputed `f ι` (`S.lvK` per position op at the plan's compile)
@[noinline] def kt {α : Type} (f : Kind → α) : Kind → α :=
  let a := f .L32; let b := f .P30; let c := f .N30
  fun ι => match ι with | .L32 => a | .P30 => b | .N30 => c

theorem kt_eq {α : Type} (f : Kind → α) : kt f = f := funext fun ι => by cases ι <;> rfl

/-- The group's representative (index `L32`): its node flag. -/
def Grp.rep (G : Grp) : KindP := G .L32

/-- Seed: `hdr`'s first 16 bytes against the selected kind's constant. -/
def seedOpsG (G : Grp) (b : ℕ) : List Op :=
  [.piField 0 0 48, .askSeed b, .piElem 0 0,
   .const (kt fun ι => .f (F.ofBytes (bytesAt (bytesOf ([(G ι).byte, (G ι).d.m.toUInt8] ++
     List.replicate 46 0)) 0 16))),
   .assertEq (b + 2) (b + 3) allK]

/-- The Merkle steps of one position (`merkleOps4`, the depth per kind). -/
def merkleOpsG (sib : Kind → ℕ) (i : ℕ) (j : Reg) : ℕ → ℕ → Reg → ℕ → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, h, cur, so, b =>
    let act : KC Bool := kt fun ι => decide (h < sib ι)
    [.piDigest 0 so, .bitOf j h, .selectHalf (b + 1) cur b, .selectHalf (b + 1) b cur,
     .askNode i h (b + 2) (b + 3) act, .keep act (b + 4) cur,
     .assertZero b (fun ι => !act ι)] ++ merkleOpsG sib i j n (h + 1) (b + 5) (so + 32) (b + 6)

/-- Z2's `targetS` operand of a segment (`segPtOp`) per kind: one length for the group. -/
def segPtOpG (S : Seq) (G : Grp) (outs : Array (List Reg)) : Op :=
  let st := outs.getD 1 []
  .packFK fun ι => ((outs.getD 3 []).drop 1).take ((G ι).d.m - 13) ++
    List.replicate (S.mStar - (G ι).d.m) (st.getD 1 0) ++ st.drop 2

/-- One position `p` of level `i` (`posOps4`, the kind's ladder per index; revision 4.4.1 (β′): ends
with the cap index, the static read of `D_r` and `assertEq cur D_r`; the cap check is the finals'
`capChkOps`). -/
def posOpsG (L : Level) (K : Kind → Level) (i co so dO : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) :
    List Op :=
  [.idx (kt fun ι => ans.getD (p / (K ι).per) 0) (fun ι => (K ι).logN) (kt fun ι => p % (K ι).per),
   .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOpsG (fun ι => (K ι).sib) i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun ι => (K ι).sib), .piDigest 0 (dO + 32 * p),
   .assertEq (curOfY L.sib (b + 3)) (b + 4 + 6 * L.sib + 1) allK]

/-- **One phase** of the group program (`genPhase4` with the kind tables per index). -/
def genPhaseG (S : Seq) (G : Grp) (n : ℕ) (ph : String × Sh) (c : GCtx) : List Op × GCtx :=
  let p := G.rep
  let b := c.next
  let o := fun f => fieldOffOf S f + phaseOffOf S n f
  let rec_ := fun (ops : List Op) (st : Reg) (out : List Reg) =>
    (ops, { c with next := b + opsOut ops, st := st, outs := c.outs.push out })
  match ph.2 with
  | .seed => rec_ (seedOpsG G b) (b + 1) [b + 1]
  | .absorb f len =>
    if f = fStmt then
      if p.d.node then rec_ (absorbOps 0 (o f) len c.st b ++ stmtOps4 p (o f) b (b + 2)) (b + 1) [b]
      else
        let b₂ := b + 2 + opsOut (stmtOps4 p (o f) b (b + 2))
        rec_ (absorbOps 0 (o f) len c.st b ++ stmtOps4 p (o f) b (b + 2) ++ lastOps (o f) b₂) (b + 1)
          (b :: lastOuts b₂)
    else if f = fFinal then rec_ (absorbOps 0 (o f) len c.st b ++ finalOps4 S p (o f) (b + 2)) (b + 1) [b]
    else if f = fLrEnd ∨ f = fEEnd then
      rec_ (absorbOps 0 (o f) len c.st b ++ [.assertZero b (fun _ => !p.d.node)]) (b + 1) [b]
    else rec_ (absorbOps 0 (o f) len c.st b) (b + 1) [b]
  | .squeezes k ch =>
    match ch with
    | .coords =>
      let rs := (List.range (2 * k)).map fun x => b + 3 * (x / 2) + 1 + x % 2
      let (ops, c') := rec_ (sqzCoordOps k c.st b ++ [.packF rs]) (b + 3 * k - 3) ((b + 3 * k) :: rs)
      (ops, { c' with pt := b + 3 * k })
    | .one => rec_ (sqzOps k c.st b ++ [.chF b 0]) (b + k - 1) [b + k]
    | .pos _ =>
      let ans := (List.range k).map (b + ·)
      let (ops, c') := rec_ (sqzOps k c.st b) (b + k - 1) ans
      (ops, { c' with posAns := ans })
  | .uni f =>
    if p.d.node then
      let (ops, c') := rec_ (uniOps 0 (o f) c.st c.pt b) (b + 2) [b + 3, b + 133, b + 134]
      (ops, { c' with uni := b + 133 })
    else
      let (ops, c') := rec_ (segPtOpG S G c.outs :: uniOps 0 (o f) c.st b (b + 1)) (b + 3)
        [b + 4, b + 134, b + 135]
      (ops, { c' with uni := b + 134 })
  | .rounds f k deg inK =>
    let init := initClaim ph.1
    let (iops, cl) := initOps init 0 (o f) inK c.uni b
    let b' := b + init.width
    let w := if inK then 13 else roundW deg
    let rs := (List.range k).map fun j => b' + w * j + 3
    let real : KC ℕ := kt fun ι => realRounds (G ι) ph.1 k
    let (ops, c') := rec_ (iops ++ roundsOps 0 (o f) deg inK real k 0 c.st cl b')
      (if k = 0 then c.st else b' + w * k - w + 2)
      (cl :: rs ++ [if k = 0 then cl else b' + w * k - 1])
    (ops, if inK then { c' with foldR := rs } else c')
  | .queries i =>
    let L := S.lv i
    let K := kt fun ι => S.lvK (G ι).d.m i
    let co := o fCols; let so := o fSibs; let dO := dOff4 S i
    let pw := posW4 S i
    let ops := [.packK c.foldR, .eqTableK b] ++ (List.range L.t).flatMap fun q =>
      posOpsG L K i co so dO c.posAns (b + 1) q (b + 2 + pw * q)
    rec_ ops c.st ((List.range L.t).map fun q => b + 2 + pw * q + 3)

/-- The phases from number `n`. -/
def genPhasesG (S : Seq) (G : Grp) : List (String × Sh) → ℕ → GCtx → List Op × GCtx
  | [], _, c => ([], c)
  | ph :: ps, n, c =>
    let r₁ := genPhaseG S G n ph c
    let r₂ := genPhasesG S G ps (n + 1) r₁.2
    (r₁.1 ++ r₂.1, r₂.2)

/-- **The group's skeleton**: every phase, from register `0`. -/
def skeletonG (S : Seq) (G : Grp) : List Op × GCtx :=
  genPhasesG S G (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **The group program `gen4G S G fin`**: the skeleton, the phase-final checks, `accept`; in mux
mode (the selector picks the kind). -/
def gen4G (S : Seq) (G : Grp) (fin : FinOps) : VProg :=
  ⟨.mux, (skeletonG S G).1 ++ fin (skeletonG S G).2.outs (skeletonG S G).2.next ++ [.accept]⟩

/-- **`finOps4` with the table relocation** (`finOps4F_eq`). -/
def finOps4F (P : FinP) (Q : Kind → FinP) : FinOps := fun outs b =>
  let tab := fieldOffT P.S
  let fo := (finalsOf P Q).ops outs b
  (fo ++ capChkOps P.S outs (b + opsOut fo)).map (relocT P.S tab)

theorem finOps4F_eq (P : FinP) (Q : Kind → FinP) (outs : Array (List Reg)) (b : ℕ) :
    finOps4F P Q outs b = finOps4 P outs b Q := by
  simp only [finOps4F, finOps4]

/-- **The node group's finals' parameters** (revision 4.3): index `ι`'s are its kind's, with its
cells (`cells`: each node kind's public cells). -/
def nodeQ (cells : NodeKind → List ℕ) : Kind → FinP := fun ι => nodeFinP (nodeAt ι) (cells (nodeAt ι))

/-- **The segment group's.** -/
def segQ : Kind → FinP := fun ι => segFinP (segAt ι)

/-- **The previous-node slot's program** (`cells`: each node kind's public cells; index `ι` verifies a
child of kind `nodeAt ι` with its cells). The counts are index `L32`'s (every index's: `FRVIR4Uni`). -/
def progNodeGK (cells : NodeKind → List ℕ) : VProg :=
  gen4G seq4 nodeGrp (finOps4F (nodeQ cells .L32) (nodeQ cells))

/-- The previous-node slot's program with one cell list for every kind (revision 4.1's signature;
the slot programs use `progNodeGK` with each kind's cells). -/
def progNodeG (cells : List ℕ) : VProg := progNodeGK fun _ => cells

/-- **A segment sub-slot's program.** -/
def progSegG : VProg := gen4G seq4 segGrp (finOps4F (segQ .L32) segQ)

/-- The slot programs' finals are `finOps4`'s. -/
theorem progG_fin (cells : NodeKind → List ℕ) :
    progNodeGK cells = gen4G seq4 nodeGrp (fun outs b => finOps4 (nodeQ cells .L32) outs b (nodeQ cells)) ∧
      progSegG = gen4G seq4 segGrp (fun outs b => finOps4 (segQ .L32) outs b segQ) := by
  simp only [progNodeGK, progSegG, ← finOps4F_eq]; exact ⟨trivial, trivial⟩

/-! ## Controls -/

/-- (+) The groups: the representative's kinds, and a smaller `m` at another index. -/
theorem grp_ctl : nodeGrp.rep = .ofNode .N4 ∧ segGrp.rep = .ofSeg .L32 ∧
    (nodeGrp .P30).d.m = 31 ∧ (segGrp .N30).d.m = 31 := ⟨rfl, rfl, rfl, rfl⟩

/-- (+) The seed constant reads the selected kind's byte: `N2`'s at index `P30`; (−) the indices
name distinct kinds. -/
theorem grp_bytes : (nodeGrp .P30).byte = 0x4D ∧ (nodeGrp .L32).byte ≠ (nodeGrp .P30).byte ∧
    (segGrp .P30).byte = 0x50 ∧ (segGrp .N30).byte ≠ (segGrp .L32).byte := by decide

/-- (+) A segment's Merkle step is active below its kind's depth only: at level 0, step 9 is active
for `L32` and not for `L30` (depth 9 at level 0). -/
theorem merkleOpsG_ctl :
    (fun ι => decide (9 < (seq4.lvK (segGrp ι).d.m 0).sib)) .L32 = true ∧
      (fun ι => decide (9 < (seq4.lvK (segGrp ι).d.m 0).sib)) .P30 = false := by
  decide

end Rev4
end FR

end G6_FRVIR4Mux
