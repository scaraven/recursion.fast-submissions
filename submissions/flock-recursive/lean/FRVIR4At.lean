-- New for `flock-recursive` (BLUEPRINT revision 4.3, changes 28, route (A); stage INT-8).
import FRVIRFinals4

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
  simp only [gFinE, hck, Bool.cond_true]
  rfl

theorem map_at_gFinB' : (gFinB' P fi b Q).1.map (Op.at h false ι) = (gFinB' P fi b (finAt Q ι)).1 := by
  simp only [gFinB']
  rfl

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
  simp only [gFinPf, hck, Bool.cond_true, List.map_append, List.map_cons, List.map_nil, map_at_ptsOps,
    List.map_flatMap, map_at_selOps, map_at_gCellsOpsK, map_at_gLvsOps, map_at_fhOps, map_at_padsOps,
    map_at_gTailOps, List.map_map]
  rfl

theorem gFinSh_ex (Q' : Kind → FinP) : (gFinSh P fi b Q).2 = (gFinSh P fi b Q').2 := by
  unfold gFinSh; cases P.vn <;> rfl

end Fields

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
  simp only [finOps4, List.map_map]
  have e : (Op.at h false ι ∘ reloc P.S) = (reloc P.S ∘ Op.at h false ι) :=
    funext (reloc_at false ι P.S hr)
  rw [e, ← List.map_map]
  refine congrArg (List.map (reloc P.S)) ?_
  have hrest : List.Forall₂ (FMap (Op.at h false ι)) (finalsOf P Q).rest (finalsOf P (finAt Q ι)).rest := by
    simp only [Finals.rest, finalsOf]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ ?_)))))
    · exact fun fi b => ⟨map_at_gFinZ h ι P Q fi b, rfl⟩
    · exact fun fi b => ⟨map_at_gFinLc h ι P Q fi b, rfl⟩
    · exact fun fi b => ⟨map_at_gFinSh h ι P Q fi b, gFinSh_ex P Q fi b _⟩
    · exact fun fi b => ⟨map_at_gFinLr h ι P Q fi b hck, rfl⟩
    · exact fun fi b => ⟨map_at_gFinE h ι P Q fi b hck, rfl⟩
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
    P.ncell = P'.ncell ∧ P.tails = P'.tails

/-- **The finals read only `P`'s counts.** -/
theorem finOps4_counts {P P' : FinP} (hc : SameCounts P P') (Q : Kind → FinP) (outs : Array (List Reg))
    (b : ℕ) : finOps4 P outs b Q = finOps4 P' outs b Q := by
  obtain ⟨hS, hf, he, hn, hv, hk, hl, ht⟩ := hc
  have hT : gFinPTop P = gFinPTop P' := by funext fi b; simp only [gFinPTop, hS]
  have hP : gFinP P = gFinP P' := by funext i; simp only [gFinP, hT]
  simp only [finOps4, finalsOf, gFinRS, gRsTail, gFinZ, gFinLc, gLcHead, gFinSh, gShCore, gBndOps, gPadB,
    gFinLr, gFinE, gFinB', hP, gFinPf, gPfPts, pfCand, pfCandA, hS, hf, he, hn, hv, hk, hl, ht]

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
