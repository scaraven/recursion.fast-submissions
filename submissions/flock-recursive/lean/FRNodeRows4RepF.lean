-- G6: this module also holds the former modules `FRSubmission4`, `FRXSig4H`, `FRSubmission4Cert`, `FRNodeLinks4Sub`, `FRNodeLinks4SigH`, `FRNodeRows4RepSegT`, `FRNodeRows4RepSeg` (one section each, in import order).
import FRSubmission4V
import FRXNd4
import FRXPf4
import FRNodeRows4AskStmtS
import FRNodeLinks4Run
import FRNodeRows4RepSegK
import FRVIRTplSegT
import FRNodeRun4Ctrl
import FRNodeRun4BL

section G6_FRSubmission4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §3, §5.5, §9; stage S-I, items 1–2): the
-- revision 4.1 `Submission` term, compiled for the badge, its completeness and `δ`.

/-!
# The revision 4.1 submission `sub4`

The fields (X4-RESULT §3):

* `V := V4F` (`FRSubmission4V`), which is `VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4`
  (`V4F_eq`), `implB := Impl.implCN`, every program and op set a closed constant.
* `P := fun _ _ w => ret (encodeF w)`: the witness-sending prover of `complete4`.
* `E := E4X nd acc` and `ext := ext4With nd`: S-H3's extractor with S-H4's node branch `nd`
  (`FRXNd4`: the decode `decF04 κ`, then the output `outIR4 κ`, per node kind).
* `ε := epsRQ`, the cast of the rational `15/2^124` (`epsRQ_eq`: it is `epsR`), so that the
  structure has compiled code (AGENTS.md: the badge compiles the whole `submission`).
* `δ := 0`, `qV := qV4 = 36000`, `fuel := X.fuel` (`3 · 2^46 + 2^13 t`).

**Completeness (residuals 8 and 9 of X4).** `complete4` (`FRVerifier4`) proves the contract's
`CompleteWithError` at `δ = 0` for every verifier `V4with Vseg Vnode` and the prover `encodeF`,
under every key: the honest proof of a witness is its witness-sending encoding, which `V4with`
accepts with no query (`V4_encode`). The contract's `Certificate.complete` asks exactly that for
the submission's own `P`, `V` and `δ` (`.contract/RecursionFast/Contract/Certificate.lean`,
`complete`), so **`complete_rev4`** and **`delta_rev4`** close both residuals with no hypothesis.
The completeness of the aggregate and node proofs that `prover.s` sends is not part of the
contract's certificate; the harness checks it concretely (`acc` of every stream output).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4
open RecursionFast.WitnessSending (encodeF)
open scoped NNReal

/-! ## The submission -/

/-- The submission without its extractor specification (whose `acc` it reads). -/
def sub0 : Submission where
  V := V4F
  P := fun _ _ w => .ret (encodeF w)
  E := fun _ _ _ => none
  ext := X.X4.ext4With X.X4.nd
  ε := epsRQ
  δ := 0
  qV := qV4
  fuel := X.fuel

/-- **The revision 4.1 submission**: `sub0` with `E := E4X nd sub0.acc`. -/
def sub4 : Submission := { sub0 with E := X.X4.E4X X.X4.nd sub0.acc }

/-- `acc` reads only `V` and `qV`. -/
theorem sub4_acc : sub4.acc = sub0.acc := rfl

theorem sub4_V : sub4.V = VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4 := V4F_eq
theorem sub4_qV : sub4.qV = qV4 := rfl
theorem sub4_E : sub4.E = X.X4.E4X X.X4.nd sub4.acc := rfl
theorem sub4_ε : sub4.ε = Snd.epsR := epsRQ_eq
theorem sub4_ext : sub4.ext = X.X4.ext4With X.X4.nd := rfl
theorem sub4_fuel : sub4.fuel = X.fuel := rfl
theorem sub4_P : sub4.P = fun _ _ w => .ret (encodeF w) := rfl

/-! ## Completeness: X4's residuals 8 and 9 -/

/-- **Residual 8, closed**: the contract's completeness of `sub4` under every key, at `δ = 0`
(`complete4`: the witness-sending path). -/
theorem complete_rev4 (vk : Digest) :
    CompleteWithError (Rel (sub4.acc vk)) (sub4.P vk) (sub4.V vk) sub4.δ :=
  complete4 VsegF VnodeF sub4 rfl rfl rfl vk

/-- **Residual 9, closed**: `δ = 0 ≤ completenessCap`. -/
theorem delta_rev4 : sub4.δ ≤ completenessCap := zero_le

/-! ## Controls -/

/-- (+) The honest proof of a one-step leaf witness is accepted with no query; (−) a node kind byte
with the wrong size is rejected with no query. -/
theorem sub4_ctrl (vk s c : Digest) :
    sub4.V vk (leafStmt (chainEnd s 1) 1) (WitnessSending.encode (.leaf s 1)) = .ret true ∧
      sub4.V vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  ⟨ctrl4_W_leaf VsegF VnodeF vk s, ctrl4_bad_node_size VsegF VnodeF vk c⟩

/-- (+) `δ = 0` is the completeness error, and (−) it is not the knowledge error's bound: the
claim's `ε` is positive. -/
theorem sub4_numbers : sub4.δ = 0 ∧ 0 < sub4.ε := by
  refine ⟨rfl, ?_⟩
  rw [sub4_ε, Snd.epsR]; positivity

end FR.Sub4

end G6_FRSubmission4

section G6_FRXSig4H

-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii); stage S-H4, pass 8, item 1:
-- `sig_of_H`). Uses S-E13b's WOTS rows (`FRNodeRows4Wots*`) and link families (`truthS4`).

/-!
# `sig_of_H`: the signature read off H is L's

On every witness of the node statement (`StmtN4`), the signature `sigH` reads from H's message
slots is the one the reader reads from L (`readSig4`). Every equality H ↔ L has a row or a link
family; no hypothesis beyond `StmtN4`:

* **the index**: the `j` family puts the `j` mirror's first eight bytes in the key leaf's message
  bytes `1 … 8`, and the index row makes the mirror L's index element (`j_byte`, `j_mirror`);
* **`ots_i`**: the `x` family puts mirror `3i` in block `3i`'s bytes `11 … 42` (`fam_byte`), and the
  chain row `x_{i,0} = ots_i` makes the mirror L's `ots_i` (`chainRowsI`, first row);
* **sibling `t`**: the `l` (`r0`, `r31`) family puts mirror `533 + t` (`549 + t`, `565 + t`) in the
  level's message bytes, and the mux rows make the `l` mirror the sibling when the index bit is `1`,
  the `r` mirror when it is `0` (`mux_rows`, `idx_bit`); byte 31 of `r` comes through the `r31`
  mirror (`r31_byte`).

The node rows `W4.xRows` hold on `StmtN4` (they are slot 1's link rows when their cell check
passes; otherwise slot 1 holds the rejecting row: `xRows_of_stmt`, S-E13a's fold).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4 FR.Circ FR.N4c FR.W4

/-- **The node rows hold on the node statement** (S-E13a's fold, `wots_aggPad_of_rows`'s split). -/
theorem xRows_of_stmt {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) : ∀ r ∈ xRows κ, r.Holds w := by
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  have hF := N4s.protoFit_of hone hE
  have h1 : 1 < κ.vslots := by cases κ <;> decide
  have hl := N4s.linkRows_hold hF h1 hE
  by_cases h : xOkK κ = true
  · intro r hr
    refine hl r (List.mem_append_right _ ?_)
    rw [extRowsC, if_pos rfl, if_pos h, xRowsK_eq]; exact List.mem_append_left _ hr
  · exfalso
    have := hl (rejR κ) (List.mem_append_right _ (by rw [extRowsC, if_pos rfl, if_neg h]; simp))
    simp [rejR, Row.Holds, hone] at this

/-- **The index read off H is L's** (`j` family, index row). -/
theorem idxH_eq {κ : NodeKind} {w : Asg} (hS : truthS4 κ w) {σ : ℕ} (hσ : σ < 2)
    (hj : w (mc κ σ 399 0) = w (Lc κ σ 0)) : idxH κ σ w = W4.idxOf κ σ w := by
  have hl : ((List.range 8).map fun k => hMB w (wb κ σ 399) (1 + k)) = enc64 (W4.idxOf κ σ w) := by
    refine list_ext_getD (by simp [enc64_length]) fun k hk => ?_
    simp only [List.length_map, List.length_range] at hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
      hMB_eq _ _ (by omega), j_byte hS hσ (by norm_num) hk hj]
  have hlt : W4.idxOf κ σ w < 2 ^ 64 := by
    unfold W4.idxOf; exact (UInt64.toNat_lt _).trans_le (by norm_num)
  rw [idxH, hl, ofLE_enc64, Nat.mod_eq_of_lt hlt]

/-- **`ots_i` read off H is L's** (`x` family, the chain's first row). -/
theorem otsH_eq {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hS : truthS4 κ w) {σ : ℕ}
    (hσ : σ < 2) (hch : ∀ r ∈ chainRows κ σ, r.Holds w) {i : ℕ} (hi : i < wotsLen) :
    hMD w (wb κ σ (3 * i)) 11 = Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) := by
  have e : ∀ h < 2, w (mc κ σ (3 * i) h) = w (otsC κ σ i h) := fun h hh => by
    have := eqR_val hone (hch _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, List.mem_cons_self ..⟩⟩))
    simpa using this
  have hd : Read.digestOf w (N4s.sigCell κ σ (1 + 2 * i)) (N4s.sigCell κ σ (2 + 2 * i)) = md κ σ (3 * i) w := by
    rw [md, digestOf_congr (e 0 (by norm_num)) (e 1 (by norm_num))]
    unfold otsC N4s.sigCell Lc; rw [show 1 + 2 * i + 1 = 2 + 2 * i by omega, Nat.add_zero]
  rw [hd]
  refine Vector.ext fun k hk => ?_
  have := fam_byte (f := 0) hS hσ (by decide) (t := 3 * i) (by simp [NodeT.fam]; unfold wotsLen at hi; omega)
    (k := k) (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
  simp only [NodeT.fam, id, Nat.zero_div, Nat.zero_add] at this
  rw [hMD, Vector.getElem_ofFn, hMB_eq _ _ (by omega), this, md_get _ _ _ _ hk]

/-- **Path sibling `t` read off H is L's** (`l`/`r0`/`r31` families, the mux rows). -/
theorem sibFH_eq {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hS : truthS4 κ w) {σ : ℕ}
    (hσ : σ < 2) (hix : ∀ r ∈ idxRows κ σ, r.Holds w) (hp : ∀ r ∈ pathRows κ σ, r.Holds w)
    {t : ℕ} (ht : t < sigHeight) : sibFH κ σ t w = sibD κ σ w t := by
  have hs : sigHeight = 16 := rfl
  have hm : ∀ h < 2, ∀ r ∈ [eqR κ (Lin.cell (hc (wb κ σ (467 + 2 * t)) h)) (Lin.cell (hc (wb κ σ (466 + 2 * t)) (2 + h))),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (sibC κ σ t h)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (mc κ σ (533 + t) h)),
       muxR (Lin.cell (ixC κ σ t)) (Lin.cell (hc (curB κ σ t) (2 + h))) (Lin.cell (sibC κ σ t h)) (Lin.cell (mc κ σ (549 + t) h))],
      r.Holds w := fun h hh r hr => hp r (pathRows_mem ht (by
        simp only [pathRowsT, List.mem_append]; exact .inl (.inl (List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr⟩))))
  have hb : w (ixC κ σ t) = 0 ∨ w (ixC κ σ t) = 1 :=
    boolR_val hone (hix _ (List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)))
  have ml := mux_rows hb (x := sibC κ σ t) (y := fun h => hc (curB κ σ t) (2 + h)) (m := mc κ σ (533 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have mr := mux_rows hb (x := fun h => hc (curB κ σ t) (2 + h)) (y := sibC κ σ t) (m := mc κ σ (549 + t))
    fun h hh => hm h hh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [sibFH, idxH_eq hS hσ (j_mirror hone hix)]
  by_cases hb1 : w (ixC κ σ t) = 1
  · have hbit : W4.idxOf κ σ w / 2 ^ t % 2 = 1 := by
      have := (idx_bit hone hix (by omega : t < 16)).not.2 (not_not.2 hb1); omega
    rw [if_pos hbit]
    rw [if_pos hb1] at ml
    rw [sibD, ← ml]
    refine Vector.ext fun k hk => ?_
    have := fam_byte (f := 5) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := k)
      (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
    simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
    rw [hMD, Vector.getElem_ofFn, hMB_eq _ _ (by omega), this, ← md, md_get _ _ _ _ hk]
  · have hbit : ¬ W4.idxOf κ σ w / 2 ^ t % 2 = 1 := by
      have := (idx_bit hone hix (by omega : t < 16)).2 hb1; omega
    rw [if_neg hbit]
    rw [if_neg hb1] at mr
    rw [sibD, ← mr]
    refine Vector.ext fun k hk => ?_
    rw [rFH, Vector.getElem_ofFn, ← md, md_get _ _ _ _ hk]
    split_ifs with h31
    · have := fam_byte (f := 6) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := k)
        (by simp [NodeT.fam]; omega) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
      rw [hMB_eq _ _ (by omega), this]
    · have := fam_byte (f := 7) hS hσ (by decide) (t := t) (by simp [NodeT.fam]; omega) (k := 0)
        (by simp [NodeT.fam]) (by decide) (by decide) (by decide)
      simp only [NodeT.fam, Nat.zero_div, Nat.zero_add] at this
      have k31 : k = 31 := by simp only [not_lt] at h31; omega
      rw [hMB_eq _ _ (by norm_num), this, r31_byte hone ht hp, k31]

/-- **`sig_of_H`**: on every witness of the node statement, the signature read off H's message
slots (`sigH`) is the one the reader reads off L (`readSig4`). -/
theorem sig_of_H {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ σ < 2, sigH κ σ w = N4s.readSig4 κ σ w := by
  have hX := xRows_of_stmt hS
  obtain ⟨-, hSh, -, -, hP⟩ := hS
  have hone := N4s.one_of_pubCells hP
  intro σ hσ
  have hMW : ∀ r ∈ wotsRows κ σ (actW κ (aggOf κ σ)), r.Holds w := fun r hr => hX r (by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hix : ∀ r ∈ idxRows κ σ, r.Holds w := fun r h => hMW r (mem_wotsRows.2 (.inl h))
  have hch : ∀ r ∈ chainRows κ σ, r.Holds w := fun r h => hMW r (mem_wotsRows.2 (.inr (.inr (.inl h))))
  have hpa : ∀ r ∈ pathRows κ σ, r.Holds w := fun r h =>
    hMW r (mem_wotsRows.2 (.inr (.inr (.inr (.inr (.inl h))))))
  have hj := j_mirror hone hix
  have e1 : (sigH κ σ w).idx = (N4s.readSig4 κ σ w).idx := idxH_eq hSh hσ hj
  have e2 : (sigH κ σ w).ots = (N4s.readSig4 κ σ w).ots :=
    List.map_congr_left fun i hi => otsH_eq hone hSh hσ hch (List.mem_range.1 hi)
  have e3 : (sigH κ σ w).path = (N4s.readSig4 κ σ w).path := by
    simp only [sigH, N4s.readSig4]
    refine List.map_congr_left fun t ht => ?_
    rw [sibFH_eq hone hSh hσ hix hpa (List.mem_range.1 ht), sibD]
    unfold sibC N4s.sigCell Lc
    rw [show 1 + 2 * wotsLen + 2 * t + 1 = 2 + 2 * wotsLen + 2 * t by omega, Nat.add_zero]
  calc sigH κ σ w = ⟨(sigH κ σ w).idx, (sigH κ σ w).ots, (sigH κ σ w).path⟩ := rfl
    _ = ⟨(N4s.readSig4 κ σ w).idx, (N4s.readSig4 κ σ w).ots, (N4s.readSig4 κ σ w).path⟩ := by
      rw [e1, e2, e3]
    _ = N4s.readSig4 κ σ w := rfl

/-- **`readW4 sigH` is the reader's node witness** on every node statement's witness `f⁽⁰⁾ = wF κ L es`
(`readW4_eq` with `sig_of_H`): the bridge S-L4's `hL_of_res` uses at `sg := sigH`. -/
theorem readW4_sigH {κ : NodeKind} {L es : Log} {vk c₁ c₂ : Digest}
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (wF κ L es)) :
    readW4 sigH κ L es = .node c₁ c₂ ((N4s.rd4 pf4).sgn κ 0 (wF κ L es)) ((N4s.rd4 pf4).sgn κ 1 (wF κ L es)) :=
  readW4_eq hS.2.2.2.2 (sig_of_H hS)

end FR.X

end G6_FRXSig4H

section G6_FRSubmission4Cert

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-I, items 1–3): the certificate of
-- the revision 4.1 submission `sub4` from INT-10's `certificate_rev4H`, with the residuals other
-- tracks still own bundled as one hypothesis, and the bounds against the rendered claim.

/-!
# `certificateR_sub4`: the certificate of `sub4`, given the open residuals

**`Open4`** is what INT-10's `certificate_rev4H`, in RSV-S3's `StmtN4R` form `certificate_rev4HR` (at `fin := finC finPf`, `lRows := Layout.lRows`,
`κs₀ := 0`, where `implC` is `implB` by `Impl.implCN_eq`) still asks for `sub4`, stated over
S-E13a's route (S-H4 pass 7, `reviews/PATH-review.md` F1): `Resid4HR.slots` is `I4`, `rd4 pf4` and
`resid4_of ∘ gap4_of_rowsI` (B4: `aggChk` from the rows; SRA: over `StmtN4R`, through RSV-S3's
`certificate_rev4HR`), so what remains of it is `Gap4R.imp` at
`pf4 = reassemble4 seq4` (`PfHdr pf4` is `pfHdr_reassemble4`, `PfView pf4` is `pfView_reassemble4`). X4's rows 1 (`FrontHi`) and 2 (`RunFacts4`) are closed;
rows 8–9 are `complete_rev4`, `delta_rev4`; row 7 (`DecOk4`) is `decOk4_nd`, proved (S-H4 pass 11).

| field | what | owner |
|---|---|---|
| `gap` | `StmtN4R → Gap4R.imp` at `pf4` (B4 closed `aggChk`, A1′ `kindS`/`wf`; SRA: over `StmtN4R`) | B3 (`gap4Imp_of_run`), IMP, C1, SRA (`gap4Imp_of_rsv`), ASK-P |
| `dec` | **`Links4 nd nodeDec4_nd`** (`hL`) | S-L4 (`links4_sigH`: from `gap`, `FRSubmission4Fin`) |

**The signature reader is fixed** (S-H4 pass 8): `sg := sigH` (H's message slots, rows 4–7), and
`readW4_sigH` (`readW4_eq` with **`sig_of_H`**, no hypothesis beyond `StmtN4`) is the bridge
`hL_of_res` uses; `sigWords_sigH` gives its output words as shifted H message words.

**The node branch is S-H4's `nd`** (`FRXNd4`, pass 11) in `sub4.E`/`sub4.ext` and in `Open4`: its
decode law `nodeDec4_nd` has links `LinksD4` and witness `readW4 sigH`, so `Open4.dec` is S-L4's
`links4_sigH` from `Open4.gap` (`FRSubmission4Fin`: `Open4F := Gaps4`).

**`certificateR_sub4`**: `Open4 → CertificateR D sub4` for every declared claim `D` whose numbers
are at least the submission's and whose fuel is within the budget (`boundsOK`); **`boundsOK_claim`**
checks them at `claim.json`'s numbers (`15/2^124`, `0`, `36000`, `3 · 2^46 + 2^13 t`).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4
open scoped NNReal

/-- The node verifier `sub4` runs (`sub4_V`). -/
noncomputable abbrev Vnode4 : NodeProgs := VnodeC (NI4F.implN4F fun _ => implB) N4c.cells4

/-- **The node links `hL`** (S-L4's `hL_of_res`): on a good log, an accepted in-domain node run
has a transcript `es` meeting the decode law's links, and the witness read off it is a witness of
the relation. -/
def Links4 (nd : X.XIR) (D : NodeDec4 nd) : Prop :=
  ∀ vk κ L c π, Snd.X4.GoodX Snd.P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (Vnode4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (sub4.acc vk) c (D.readW κ L es)

/-- **The circuit's open gaps** at the slots' proof decoder `pf4`: S-E13a's `Gap4R` without
`aggChk` (B4's `aggChk_of_rows`), i.e. `Gap4R.imp`: every active slot's run and imports, on every
witness of the node statement **with the reserve** (`StmtN4R`, revision 4.4.2: the reserve's cells
hold the node's child claim `ch` and the claim is true; the accepted run gives both, `nodeRunRL4`).
The reserve is what binds slot 0's `evalM` outputs (`gap4Imp_of_rsv`). -/
def Gaps4 : Prop :=
  ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
    ∀ v, N4c.Active4 (N4s.rd4 X.pf4) κ w v →
      N4s.SlotImp implB (fun _ => implB) κ v w (N4c.slotIn (N4s.rd4 X.pf4) κ vk c₁ w v)
        ((N4s.rd4 X.pf4).slotTr κ v w)

/-- **The residuals of revision 4.1's certificate still open** (owners in the module doc). -/
structure Open4 : Prop where
  gap : Gaps4
  dec : Links4 nd nodeDec4_nd

/-- `PfHdr pf4` (`pfHdr_reassemble4`). -/
theorem pfHdr_pf4 : N4s.PfHdr X.pf4 := fun e tr => X.pfHdr_reassemble4 e tr

/-- `PfView pf4` (`pfView_reassemble4`). -/
theorem pfView_pf4 : N4s.PfView X.pf4 := fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr

/-- **S-N2's `Gap4` from `Gaps4`** (B4's `gap4_of_rowsI`: the rows give everything but `imp`). -/
theorem gap4_of_gaps (hG : Gaps4) {vk : Digest} {κ : NodeKind} {w : Circ.Asg} {c₁ c₂ : Digest}
    {ch : List F} (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch) :
    N4s.Gap4 implB (fun _ => implB) X.pf4 κ vk c₁ c₂ w :=
  N4s.gap4_of_rowsI (pf := X.pf4) pfHdr_pf4 pfView_pf4 hS.1 (hG vk κ w c₁ c₂ ch hS)

/-- (Converse) **`Gaps4` asks nothing beyond IMP's `StmtN4` form** (rev44 `616b57c`): `StmtN4R`
implies `StmtN4`, so the hypothesis only shrank. -/
theorem gaps4_of_N (h : ∀ vk κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    ∀ v, N4c.Active4 (N4s.rd4 X.pf4) κ w v →
      N4s.SlotImp implB (fun _ => implB) κ v w (N4c.slotIn (N4s.rd4 X.pf4) κ vk c₁ w v)
        ((N4s.rd4 X.pf4).slotTr κ v w)) : Gaps4 :=
  fun vk κ w c₁ c₂ _ hS => h vk κ w c₁ c₂ hS.1

/-- (Converse) `Gaps4` asks nothing beyond `Gap4R` (its `imp` field). -/
theorem gaps4_of_gap4R (h : ∀ vk κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    N4s.Gap4R implB (fun _ => implB) X.pf4 κ vk c₁ c₂ w) : Gaps4 :=
  fun vk κ w c₁ c₂ _ hS => (h vk κ w c₁ c₂ hS.1).imp

/-- **`Resid4HR` from `Open4`'s parts**: the slots are `I4`, `rd4 pf4` with
`resid4_of ∘ gap4_of_rows` over `StmtN4R`; the links are `Links4`. -/
theorem resid4H_of {nd : X.XIR} {D : NodeDec4 nd} (hG : Gaps4) (hL : Links4 nd D) (vk : Digest) :
    Snd.R4.Resid4HR (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk := by
  exact ⟨⟨N4s.I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _, N4s.rd4 X.pf4,
    N4s.I4_rows _ _ _ _, fun κ w c₁ c₂ _ hS => N4s.resid4_of _ _ X.pf4 hS.1 (gap4_of_gaps hG hS)⟩,
    fun κ L c π hG' hk hd hr => hL vk κ L c π hG' hk hd hr⟩

/-- **The contract's `Certificate` of `sub4`, given `Open4`** (RSV-S3's `certificate_rev4HR`: the
residual over `StmtN4R`; `DecOk4 nd` proved, `decOk4_nd`). -/
theorem certificate_sub4 (h : Open4) : Certificate sub4 :=
  Snd.R4.certificate_rev4HR (Impl.finC finPf) Layout.lRows 0 sub4 sub4_V sub4_qV sub4_E sub4_ε
    sub4_ext sub4_fuel decOk4_nd nodeDec4_nd (resid4H_of h.gap h.dec) complete_rev4 delta_rev4

/-- **The bounds of `CertificateR`** against a declared claim `D`. -/
def boundsOK (D : Declared) : Prop :=
  sub4.ε ≤ D.ε ∧ sub4.δ ≤ D.δ ∧ sub4.qV ≤ D.qV ∧ ∀ t, sub4.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t

/-- **The certificate against a declared claim**, given `Open4`. -/
theorem certificateR_sub4 (D : Declared) (hb : boundsOK D) (h : Open4) : CertificateR D sub4 :=
  ⟨certificate_sub4 h, hb⟩

/-- **The bounds at `claim.json`'s numbers** (the rendered forms of `render-challenge.py`). -/
theorem boundsOK_claim :
    boundsOK ⟨(15 : ℝ≥0) / 21267647932558653966460912964485513216, (0 : ℝ≥0) / 1, 36000,
      fun t => 211106232532992 + 8192 * t⟩ := by
  refine ⟨?_, by simp [sub4, sub0], le_of_eq rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
  · rw [sub4_ε, Snd.epsR]; norm_num
  · simp [sub4, sub0, X.fuel, X.fuelBase, X.fuelPerWord]
  · simp only [extractorBudget]; omega

/-- (−) **The bounds are not vacuous**: a declared query bound below `qV4` fails them. -/
theorem not_boundsOK_qV :
    ¬ boundsOK ⟨(15 : ℝ≥0) / 21267647932558653966460912964485513216, 0, qV4 - 1,
      fun t => 211106232532992 + 8192 * t⟩ := fun h => by
  have h1 := h.2.2.1
  have h2 : 0 < qV4 := by decide
  simp only [sub4, sub0] at h1
  omega

end FR.Sub4

end G6_FRSubmission4Cert

section G6_FRNodeLinks4Sub

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; track S-L4): `Open4`'s `Links4` (the
-- named `hL` of `sub4`) from `Gaps4` and the H signature, for S-H4's decoder.

/-!
# `Links4` of `sub4` from `Gaps4` and `SigH4`

**`links4_of_gaps`**: for a node decoder `D` whose links follow from `LinksD4` and whose witness is
`readW4 sg` (S-H4's `nd`), `Links4 nd D` follows from `Open4.gap` (`Gaps4`, S-E13a's route at
`pf4`: `resid4_of ∘ gap4_of_rows` over `StmtN4R`, as `resid4H_of`; `hL_of_sigR`) and **`SigH4 sg`** at every key. So once `nd`
lands, `Open4.dec` is `SigH4 sg` (S-G/S-E's `sig_of_H`) and nothing else.
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **`Links4` from the circuit's gaps and the H signature.** -/
theorem links4_of_gaps {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg)
    (hsig : ∀ vk, Snd.L4.SigH4 sg vk) (hG : Gaps4) : Links4 nd D := fun vk =>
  Snd.L4.hL_of_sigR (Impl.finC finPf) Layout.lRows 0 sub4 vk sub4_V sub4_qV D hLk hW (hsig vk)
    (N4s.I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _) (N4s.I4_rows _ _ _ _)
    fun κ w c₁ c₂ _ hS => N4s.resid4_of _ _ X.pf4 hS.1 (gap4_of_gaps hG hS)

/-- **`Resid4HR` of `sub4`** from the same: `resid4H_of` with `links4_of_gaps`. -/
theorem resid4H_of_gaps {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg)
    (hsig : ∀ vk, Snd.L4.SigH4 sg vk) (hG : Gaps4) (vk : Digest) :
    Snd.R4.Resid4HR (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk :=
  resid4H_of hG (links4_of_gaps D hLk hW hsig hG) vk

end FR.Sub4

end G6_FRNodeLinks4Sub

section G6_FRNodeLinks4SigH

-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii); track S-L4): `Links4` for S-H4's
-- decoder at the H signature reader `sigH` (S-H4 pass 8's `readW4_sigH`, `sig_of_H`).

/-!
# `Links4` at `readW4 sigH`

S-H4 pass 8 proves `sig_of_H` from `StmtN4` alone, and its bridge **`readW4_sigH`**: on `StmtN4` at
`wF κ L es`, `readW4 sigH κ L es` is `rd4 pf4`'s node witness. So:

* **`readW4_sigH_law`**: `readW4 sigH` meets the read law `ReadW4` at `rd4 pf4`, at every key;
* **`sigH4_sigH`**: `SigH4 sigH vk` (S-L4's name for `sig_of_H`);
* **`links4_sigH`**: for a decoder with links `⊇ LinksD4` and witness `readW4 sigH`,
  `Links4 nd D` follows from `Gaps4` alone. `Open4`'s `dec` then needs nothing beyond `gap`.
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **`readW4 sigH` meets the read law at `rd4 pf4`** (`readW4_sigH`, `wF = T4.fF`). -/
theorem readW4_sigH_law (vk : Digest) : Snd.L4.ReadW4 (X.readW4 X.sigH) (N4s.rd4 X.pf4) vk := by
  intro κ L es c₁ c₂ hS
  rw [← Snd.L4.wF_eq_fF] at hS ⊢
  exact X.readW4_sigH hS

/-- **`sig_of_H` is `SigH4 sigH`.** -/
theorem sigH4_sigH (vk : Digest) : Snd.L4.SigH4 X.sigH vk := fun _ _ _ _ hS => X.sig_of_H hS

/-- **`Links4` of S-H4's decoder from `Gaps4` alone** (links `⊇ LinksD4`, witness `readW4 sigH`). -/
theorem links4_sigH {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (hW : D.readW = X.readW4 X.sigH)
    (hG : Gaps4) : Links4 nd D :=
  links4_of_gaps D hLk hW sigH4_sigH hG

/-- **`Resid4HR` of `sub4`** for that decoder, from `Gaps4` alone. -/
theorem resid4H_sigH {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (hW : D.readW = X.readW4 X.sigH)
    (hG : Gaps4) (vk : Digest) : Snd.R4.Resid4HR (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk :=
  resid4H_of hG (links4_sigH D hLk hW hG) vk

end FR.Sub4

end G6_FRNodeLinks4SigH

section G6_FRNodeRows4RepSegT

-- New for `flock-recursive` (SEG-R §4.2–4.3, stage SEG-R1b): prototype 1's `targetS` and `shiftTarget` replays.

/-!
# The segment program's `targetS` and `shiftTarget` replays (`KOpD`s on `rtKD`)

* **`kTSS`** (`targetS r`, `r : AF 37`): canonical inputs = the 37 entries of `r` (`tssLay`), no forced
  positions; template `Tpl.tsSegT` (55 gates, 18 forcing rows `L_l · L_l = L_l`). **`kTSS_ok`**: `KOkD` at
  every index, no hypothesis (`implSeg`'s `targetS` at a leaf kind is `targetSSegI`).
* **`kSTS`** (`shiftTarget τ θ bnd κs`, types `[af 18, af 10, af 22, f]`): canonical inputs = the 51
  encoding entries (`stsLay`); template `Tpl.stSegT` (789 gates, 512 bit locals, 516 forcing rows).
  **`kSTS_ok`**: `KOkD` at every index, given that the base's `shiftTarget` is `shiftTargetI` (`SegBase`).
* Operand types other than these get the rejecting row (`kdRows`' `inOk` check).

SEG-R2: the definitions (`kTSS`, `kSTS`) moved verbatim to `FRNodeRows4SegD` (below `FRNodeRows4`, so that the
fold names them); the theorems stay here.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `targetS` -/


theorem tssIn_eq {ts : List Ty} (h : tssIn ts = true) : ts = [.af 37] := by
  unfold tssIn at h; split at h
  · rfl
  · exact absurd h Bool.false_ne_true

/-- **`targetS`'s replay obligation holds at every index** (no hypothesis). -/
theorem kTSS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kTSS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  obtain rfl := tssIn_eq hin
  simp only [kTSS, tsArgs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨a, ha, hs⟩ := val_af hty
  have hv : (implP impl₀ base 1 ι).targetS ι (rd regs r).toAF = Rev4.targetSSegI a := by
    simp only [implP, one_ne_zero, ite_false, OpImpl.fixK, implSeg, ha, Val.toAF]
    rfl
  rw [hv]
  refine ⟨by simp [tyOf, Rev4.targetSSegI, Impl.targetSLeafI, kTSS], fun cst _ e h1 hinp _ => ?_⟩
  have hx : (kTSS.args (.targetS r) ι).flatMap (fun a => encV (rd regs a)) = a.toList := by
    simp [kTSS, tsArgs, ha, encV]
  rw [hx] at hinp
  refine GM.ok_mono (ok_tsSegT h1 cst a fun p hp => ?_) fun o ho hr => ?_
  · rw [hinp p hp]; simp [kTSS, tssLay, hp, arr_getD]
  · rw [ho hr]; simp [encV]

/-! ## `shiftTarget` -/


theorem stsIn_eq {ts : List Ty} (h : stsIn ts = true) : ts = [.af 18, .af 10, .af 22, .f] := by
  unfold stsIn at h; split at h
  · rfl
  · exact absurd h Bool.false_ne_true

/-- **`shiftTarget`'s replay obligation holds at every index** (the base's `shiftTarget` is
`shiftTargetI`). -/
theorem kSTS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hS : impl₀.shiftTarget = Impl.shiftTargetI)
    (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kSTS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t h bd ks
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  obtain rfl := stsIn_eq hin
  simp only [kSTS, stArgs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨τ, hτ, hτs⟩ := val_af hty.1
  obtain ⟨θ, hθ, hθs⟩ := val_af hty.2.1
  obtain ⟨bn, hbn, hbs⟩ := val_af hty.2.2.1
  obtain ⟨κ, hκ⟩ := val_f hty.2.2.2
  have hv : (implP impl₀ base 1 ι).shiftTarget (rd regs ks).toF (rd regs t).toAF (rd regs h).toAF
      (rd regs bd).toAF = Impl.shiftTargetI κ τ θ bn := by
    rw [hτ, hθ, hbn, hκ]
    show impl₀.shiftTarget _ _ _ _ = _
    rw [hS]; rfl
  rw [hv]
  refine ⟨rfl, fun cst _ e h1 hinp _ => ?_⟩
  have hx : (kSTS.args (.shiftTarget t h bd ks) ι).flatMap (fun a => encV (rd regs a)) =
      τ.toList ++ θ.toList ++ bn.toList ++ [κ] := by
    simp [kSTS, stArgs, hτ, hθ, hbn, hκ, encV]
  rw [hx] at hinp
  have hi : ∀ p < 51, e.inp p = (τ.toList ++ θ.toList ++ bn.toList ++ [κ]).getD p 0 := fun p hp => by
    rw [hinp p hp]; simp [kSTS, stsLay, hp]
  have lτ : τ.toList.length = 18 := by simp [hτs]
  have lθ : θ.toList.length = 10 := by simp [hθs]
  have lb : bn.toList.length = 22 := by simp [hbs]
  refine GM.ok_mono (ok_stSegT h1 cst κ τ θ bn (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_) ?_)
    fun o ho hr => ?_
  · rw [hi l (by omega), List.append_assoc, List.append_assoc, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), List.append_assoc, List.append_assoc, show 18 + l = τ.toList.length + l by omega,
      getD_append_right, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), List.append_assoc, show 28 + l = (τ.toList ++ θ.toList).length + l by simp [lτ, lθ],
      getD_append_right, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), show 50 = (τ.toList ++ θ.toList ++ bn.toList).length + 0 by simp [lτ, lθ, lb],
      getD_append_right]
    rfl
  · rw [ho hr]; simp [encV]

/-! ## Controls -/

/-- (+) `targetS` is covered; (−) nothing else is (`shiftTarget`). -/
theorem kTSS_cov : kTSS.cov (.targetS 3) = true ∧ kTSS.cov (.shiftTarget 0 1 2 3) = false := by decide

/-- (+) `shiftTarget` is covered; (−) nothing else is (`targetS`). -/
theorem kSTS_cov : kSTS.cov (.shiftTarget 0 1 2 3) = true ∧ kSTS.cov (.targetS 3) = false := by decide

/-- (+) The segment's `targetS` operand `AF 37` is served; (−) not another width (a node's `r`), nor two
operands. -/
theorem tssIn_ctl : tssIn [.af 37] = true ∧ tssIn [.af 36] = false ∧ tssIn [.af 37, .af 37] = false := by
  decide

/-- (+) The segment's `shiftTarget` operands are served; (−) not a `bnd` of another width (a node's),
nor `τ` of 16 coordinates, nor a `K` `κs`. -/
theorem stsIn_ctl : stsIn [.af 18, .af 10, .af 22, .f] = true ∧ stsIn [.af 18, .af 10, .af 4, .f] = false ∧
    stsIn [.af 16, .af 10, .af 22, .f] = false ∧ stsIn [.af 18, .af 10, .af 22, .k] = false := by decide

/-- (+) The canonical inputs read the whole encoding; (−) nothing past it. -/
theorem lay_ctl : tssLay [] 36 = some 36 ∧ tssLay [] 37 = none ∧ stsLay [] 50 = some 50 ∧ stsLay [] 51 = none := by
  decide

/-- (−) **A non-Boolean `L` entry fails its forcing row** (`targetS`'s range factor reads `L`'s bits). -/
theorem tsRow_neg {e : Env} {x : F} (hx : e.inp 19 = x) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ¬ RowT.Holds e ⟨I 19, I 19, I 19⟩ := fun h => by
  simp only [RowT.Holds, ev_I, hx] at h
  rcases bool_of_row h with h' | h'
  · exact h0 h'
  · exact h1 h'

/-- (−) **A flipped digest bit fails the pack row**: two Boolean bit vectors packing to the same half
agree everywhere (`shiftTarget`'s decomposition is unique). -/
theorem pack_neg {v v' : ℕ → F} {h : F} (hb : ∀ q < 128, v q = 0 ∨ v q = 1) (hb' : ∀ q < 128, v' q = 0 ∨ v' q = 1)
    (hp : ∑ q ∈ Finset.range 128, W4.E q * v q = h) {j : ℕ} (hj : j < 128) (hne : v' j ≠ v j) :
    ∑ q ∈ Finset.range 128, W4.E q * v' q ≠ h := fun hp' =>
  hne (by rw [bits_of_pack hb' hp' ⟨j, hj⟩, bits_of_pack hb hp ⟨j, hj⟩])

end N4s
end FR

end G6_FRNodeRows4RepSegT

section G6_FRNodeRows4RepSeg

-- New for `flock-recursive` (SEG-R §4, stage SEG-R1): prototype 1's replay templates.

/-!
# The segment program's replay ops (prototype 1)

* **`kRSS`** (`rsWeight`): covers an `rsWeight` whose `act` is false at every index (so `β` is unread,
  `β = 1`) with three claims at every index; serves the operand types `[af 7, f, f, ak m ×4]`,
  `23 ≤ m ≤ 25`; forces the claims' `f₁` to zero (`F`-points); one `Tpl.rsSegT` instance.
  **`rsWeightF_seg`**: at those operands `Impl.rsWeightF r ps κ 1 ρ` is `Tpl.rsSegV` (the kind factor of
  claim 2 collapses at `β = 1`, `kwSL_one`; the narrower kinds' coordinates padded with `0`).
  **`kRSS_ok`**: `KOkD` at every index, given that the base's `rsWeight` is `rsWeightF` (`SegBase`).
* Operands of any other shape get the rejecting row (`kdRows`); an `rsWeight` with some `act` true or
  another claim count is not covered (it stays an import: no segment program has one, SEG-R0 §6).
* `targetS` and `shiftTarget` (`kTSS`, `kSTS`, SEG-R1b) are in `FRNodeRows4RepSegT`; `rtSeg1` chains all
  five of the segment program's replay ops.

SEG-R2: the definitions (`kRSS`, `rtSeg1`, `rtC1d`) moved verbatim to `FRNodeRows4SegD` (below `FRNodeRows4`, so that the
fold names them); the theorems stay here.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-- **The base ops a segment slot replays** (the certificate's `implB`: `rfl`). -/
def SegBase (impl₀ : OpImpl) : Prop := impl₀.rsWeight = Impl.rsWeightF ∧ impl₀.shiftTarget = Impl.shiftTargetI

/-! ## `rsWeight`'s value at `β = 1` and `F`-point claims -/

theorem ofF_f₀ {x : K} (h : x.f₁ = 0) : K.ofF x.f₀ = x := K_ext' rfl (by rw [h]; rfl)

theorem sqIter_zeroK (k : ℕ) : sqIter k (0 : K) = 0 := by
  rw [sqIter_eq, zero_pow (by positivity)]

theorem sqIter_oneK (k : ℕ) : sqIter k (1 : K) = 1 := by
  rw [sqIter_eq, one_pow]

/-- **`eq` on two lists of length `m ≤ n`, padded to `n` coordinates** (characteristic two). -/
theorem eqPts_pad : ∀ (q ρ : List K) (n : ℕ), q.length = ρ.length → q.length ≤ n →
    eqPts q ρ = ((List.range n).map fun l => 1 + q.getD l 0 + ρ.getD l 0).prod
  | [], [], n, _, _ => by rw [eqPts]; simp
  | x :: q, y :: ρ, n + 1, hl, hn => by
    have hc : x * y + (1 - x) * (1 - y) = 1 + x + y := by
      have := Impl.eqPtsC_eq [x] [y]; simpa [Impl.eqPtsC, eqPts] using this.symm
    rw [eqPts_cons, eqPts_pad q ρ n (by simpa using hl) (by simp at hn; omega), List.range_succ_eq_map,
      List.map_cons, List.prod_cons, List.map_map, hc]
    simp [Function.comp_def]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | _ :: _, _ :: _, 0, _, hn => by simp at hn

/-- One claim's `eq` at stage `k`, as the template's product. -/
theorem eqPts_stage (a ρ : Array K) (m : ℕ) (ha : a.size = m) (hρ : ρ.size = m) (hm : m ≤ 25)
    (hf : ∀ x ∈ a.toList, x.f₁ = 0) (k : ℕ) :
    eqPts (a.toList.map (sqIter k)) ρ.toList =
      ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a.toList.getD l 0).f₀) + ρ.toList.getD l 0).prod := by
  rw [eqPts_pad _ _ 25 (by simp [ha, hρ]) (by simp [ha, hm])]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  rw [← Impl.sqIter_ofF, ← sqIter_zeroK k, getD_map', sqIter_zeroK]
  congr 3
  rw [List.getD_eq_getElem?_getD]
  rcases h : a.toList[l]? with _ | x
  · rfl
  · exact (ofF_f₀ (hf x (List.mem_of_getElem? h))).symm

theorem phiTable_getD (r : Array F) (k : ℕ) : (phiTable r.toList).getD k 0 = (phiTable r.toList).toList.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **`rsWeight` at prototype 1** (`β = 1`, three `F`-point claims of `m` coordinates, `23 ≤ m ≤ 25`)
**is the template's value.** -/
theorem rsWeightF_seg (r : Array F) (hr : r.size = 7) (a₀ a₁ a₂ ρ : Array K) (m : ℕ) (hm : 23 ≤ m)
    (hm' : m ≤ 25) (h₀ : a₀.size = m) (h₁ : a₁.size = m) (h₂ : a₂.size = m) (hρ : ρ.size = m)
    (hf₀ : ∀ x ∈ a₀.toList, x.f₁ = 0) (hf₁ : ∀ x ∈ a₁.toList, x.f₁ = 0) (hf₂ : ∀ x ∈ a₂.toList, x.f₁ = 0)
    (κ : F) :
    Impl.rsWeightF r [a₀, a₁, a₂] κ 1 ρ = rsSegV r.toList κ ((List.range 25).map fun l => ρ.toList.getD l 0)
      (fun j l => (([a₀, a₁, a₂].getD j #[]).toList.getD l 0).f₀) := by
  rw [Impl.rsWeightF_eq, Impl.rsWeight_meets _ _ _ _ _ hr (by omega), rsSegV_eq3]
  have hρ' : ∀ l < 25, ((List.range 25).map fun l => ρ.toList.getD l 0).getD l 0 = ρ.toList.getD l 0 :=
    fun l hl => getD_range_map _ hl 0
  have hst : ∀ (a : Array K), a.size = m → (∀ x ∈ a.toList, x.f₁ = 0) → ∀ k,
      ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a.toList.getD l 0).f₀) +
        ((List.range 25).map fun l => ρ.toList.getD l 0).getD l 0).prod = eqPts (a.toList.map (sqIter k)) ρ.toList :=
    fun a ha hf k => by
      rw [eqPts_stage a ρ m ha hρ hm' hf k]
      exact congrArg List.prod (List.map_congr_left fun l hl => by rw [hρ' l (List.mem_range.1 hl)])
  have hkw : ∀ k, Impl.kwSL (sqIter k (K.ofF 1)) (a₁.toList.map (sqIter k)) ρ.toList = eqPts (a₁.toList.map (sqIter k)) ρ.toList :=
    fun k => by
      have h1K : K.ofF 1 = 1 := map_one K.ofFRingHom
      rw [h1K, sqIter_oneK]
      exact Snd.kwSL_one _ _ (by simp [h₁, hρ]) (by simp [hρ, hm])
  have hzi : [a₀, a₁, a₂].zipIdx = [(a₀, 0), (a₁, 1), (a₂, 2)] := rfl
  simp only [Impl.rsWeightS, hzi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, pow_zero, one_mul, pow_one, zero_ne_one, ite_false, ite_true,
    show (2 : ℕ) ≠ 1 by norm_num, hkw]
  simp only [List.getD_cons_zero, List.getD_cons_succ, phiTable_getD, hst a₀ h₀ hf₀, hst a₁ h₁ hf₁,
    hst a₂ h₂ hf₂, pow_two]
  rw [show K.ofF (κ * κ) = K.ofF κ * K.ofF κ from map_mul K.ofFRingHom κ κ]
  ring

theorem rsSegV_congr (rv rv' : List F) (κ κ' : F) (ρ ρ' : List K) (a a' : ℕ → ℕ → F) (hr : rv = rv')
    (hκ : κ = κ') (hρ : ρ = ρ') (ha : ∀ j < 3, ∀ l < 25, a j l = a' j l) : rsSegV rv κ ρ a = rsSegV rv' κ' ρ' a' := by
  subst hr hκ hρ
  unfold rsSegV
  refine Finset.sum_congr rfl fun j hj => congrArg _ (Finset.sum_congr rfl fun k _ => congrArg _
    (congrArg List.prod (List.map_congr_left fun l hl => ?_)))
  rw [ha j (Finset.mem_range.1 hj) l (List.mem_range.1 hl)]

/-! ## `rsWeight`'s `KOpD` -/


theorem rssIn_eq {ts : List Ty} (h : rssIn ts = true) :
    ∃ m, ts = [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] ∧ 23 ≤ m ∧ m ≤ 25 := by
  unfold rssIn at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨_, rfl, h1, h2⟩
  · simp at h

theorem implP1_rsWeight {impl₀ : OpImpl} {base : NodeKind → OpImpl} (ι : Kind) :
    (implP impl₀ base 1 ι).rsWeight = impl₀.rsWeight := rfl

theorem flatMap_encV_k (v : K) : [Val.k v].flatMap encV = encK v := by simp [encV]

/-- The encoding's entry at `pre.length + i`. -/
theorem getD_at {pre mid post : List F} {i n : ℕ} (hn : pre.length = n) (hi : i < mid.length) :
    (pre ++ mid ++ post).getD (n + i) 0 = mid.getD i 0 := by
  subst hn; exact getD_mid pre mid post hi

/-- **`rsWeight`'s replay obligation holds at every index** (the base's `rsWeight` is `rsWeightF`). -/
theorem kRSS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hR : impl₀.rsWeight = Impl.rsWeightF)
    (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kRSS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r ps κ' β act ρ
  simp only [kRSS, isRSS, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  have hact : act ι = false := hc.1 ι (by cases ι <;> simp [kinds])
  have hps : (ps ι).length = 3 := hc.2 ι (by cases ι <;> simp [kinds])
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq, hact, Bool.false_eq_true, ite_false] at hev
  obtain ⟨rfl, -⟩ := hev
  refine ⟨rfl, fun cst hz e h1 hinp hcst => ?_⟩
  obtain ⟨m, rfl, hm1, hm2⟩ := rssIn_eq hin
  obtain ⟨p0, p1, p2, hp⟩ : ∃ p0 p1 p2, ps ι = [p0, p1, p2] := by
    rcases h : ps ι with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨_, _⟩⟩⟩⟩ <;> rw [h] at hps <;> simp at hps
    exact ⟨p0, p1, p2, rfl⟩
  simp only [kRSS, rsArgs, hp, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at hty
  obtain ⟨hr, hκ, hβ, hρ, h0, h1', h2, -⟩ := hty
  obtain ⟨ra, hra, hrs⟩ := val_af hr
  obtain ⟨κv, hκv⟩ := val_f hκ
  obtain ⟨βv, hβv⟩ := val_f hβ
  obtain ⟨ρa, hρa, hρs⟩ := val_ak hρ
  obtain ⟨a0, ha0, ha0s⟩ := val_ak h0
  obtain ⟨a1, ha1, ha1s⟩ := val_ak h1'
  obtain ⟨a2, ha2, ha2s⟩ := val_ak h2
  have hx : (kRSS.args (.rsWeight r ps κ' β act ρ) ι).flatMap (fun a => encV (rd regs a)) =
      ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) := by
    simp only [kRSS, rsArgs, hp, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hra, hκv, hβv, hρa, ha0, ha1, ha2, encV]
    simp
  rw [hx] at hz hinp
  have hlr : ra.toList.length = 7 := by simp [hrs]
  have hlρ : (ρa.toList.flatMap encK).length = 2 * m := by rw [length_flatMap_encK]; simp [hρs]
  have hla : ∀ a : Array K, a.size = m → (a.toList.flatMap encK).length = 2 * m := fun a ha => by
    rw [length_flatMap_encK]; simp [ha]
  have hM : rssM [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] = m := rfl
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
    (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) := ⟨_, rfl⟩
  rw [← hxs] at hz hinp
  have hinp' : ∀ p < 133, e.inp p = ((rssLay [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] p).map fun q =>
      xs.getD q 0).getD 0 := hinp
  have hz' : ∀ q ∈ rssZf [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m], xs.getD q 0 = 0 := hz
  have hL : ∀ a : Array K, (a.toList.flatMap encK).length = 2 * a.size := fun a => by
    rw [length_flatMap_encK, Array.length_toList]
  -- the encoding's entries
  have hpre : (ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK).length = 9 + 2 * m := by
    simp only [List.length_append, hL, Array.length_toList, hrs, hρs, List.length_cons, List.length_nil] <;> omega
  have hcl : ∀ j < 3, ∀ q < 2 * m, xs.getD (9 + 2 * m + 2 * m * j + q) 0 =
      (([a0, a1, a2].getD j #[]).toList.flatMap encK).getD q 0 := by
    intro j hj q hq
    interval_cases j
    · rw [hxs, ← List.append_assoc, show 9 + 2 * m + 2 * m * 0 + q = 9 + 2 * m + q by ring,
        getD_at hpre (by rw [hL, ha0s]; omega)]; rfl
    · rw [hxs, ← List.append_assoc, ← List.append_assoc,
        show 9 + 2 * m + 2 * m * 1 + q = (9 + 2 * m + 2 * m) + q by ring,
        getD_at (by rw [List.length_append, hpre, hL, ha0s]) (by rw [hL, ha1s]; omega)]; rfl
    · rw [hxs, ← List.append_assoc, ← List.append_assoc, ← List.append_nil (a2.toList.flatMap encK),
        ← List.append_assoc, show 9 + 2 * m + 2 * m * 2 + q = (9 + 2 * m + 2 * m + 2 * m) + q by ring,
        getD_at (by rw [List.length_append, List.length_append, hpre, hL, hL, ha0s, ha1s]) (by rw [hL, ha2s]; omega)]; rfl
  have hρx : ∀ q < 2 * m, xs.getD (9 + q) 0 = (ρa.toList.flatMap encK).getD q 0 := fun q hq => by
    rw [hxs, show ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) =
        (ra.toList ++ [κv, βv]) ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) from rfl,
      getD_at (by simp [hrs]) (by rw [hL, hρs]; omega)]
  have hrx : ∀ q < 7, xs.getD q 0 = ra.toList.getD q 0 := fun q hq => by
    rw [hxs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
      List.getElem?_append_left (by simp [hrs]; omega)]
  have hκx : xs.getD 7 0 = κv := by
    rw [hxs, List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by simp [hrs])]
    simp [hrs]
  -- the claims' coordinates are `F`-points
  have hfz : ∀ j < 3, ∀ x ∈ ([a0, a1, a2].getD j #[]).toList, x.f₁ = 0 := by
    intro j hj x hx'
    obtain ⟨l, hl, hxl⟩ := List.getElem_of_mem hx'
    have hsz : ([a0, a1, a2].getD j #[]).size = m := by interval_cases j <;> assumption
    have hl' : l < m := by rw [Array.length_toList, hsz] at hl; exact hl
    have hq := hz' (10 + 2 * m + 2 * m * j + 2 * l) (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
      List.mem_map.2 ⟨l, List.mem_range.2 (by rw [hM]; exact hl'), by rw [hM]⟩⟩)
    rw [show 10 + 2 * m + 2 * m * j + 2 * l = 9 + 2 * m + 2 * m * j + (2 * l + 1) by ring,
      hcl j hj _ (by omega), (encK_getD _ l).2, List.getD_eq_getElem _ _ hl, hxl] at hq
    exact hq
  -- the canonical inputs' values
  have hin7 : ∀ p < 7, e.inp p = ra.toList.getD p 0 := fun p hp => by
    rw [hinp' p (by omega)]
    simp only [rssLay, if_pos (show p < 8 by omega), Option.map_some, Option.getD_some]
    exact hrx p hp
  have hinκ : e.inp 7 = κv := by
    rw [hinp' 7 (by norm_num)]
    simp only [rssLay, if_pos (show 7 < 8 by norm_num), Option.map_some, Option.getD_some]
    exact hκx
  have hinρ : ∀ l < 25, (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K) = ρa.toList.getD l 0 := fun l hl => by
    rw [hinp' _ (by omega), hinp' _ (by omega)]
    simp only [rssLay, hM, show ¬ 8 + 2 * l < 8 by omega, show ¬ 9 + 2 * l < 8 by omega,
      show 8 + 2 * l < 58 by omega, show 9 + 2 * l < 58 by omega, ite_false, ite_true,
      show (8 + 2 * l - 8) / 2 = l by omega, show (9 + 2 * l - 8) / 2 = l by omega]
    by_cases hlm : l < m
    · simp only [hlm, ite_true, Option.map_some, Option.getD_some, show 8 + 2 * l + 1 = 9 + 2 * l by ring,
        show 9 + 2 * l + 1 = 9 + (2 * l + 1) by ring]
      rw [hρx _ (by omega), hρx _ (by omega), (encK_getD _ l).1, (encK_getD _ l).2]
    · simp only [hlm, ite_false, Option.map_none, Option.getD_none]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hρs]; omega)]; rfl
  have hina : ∀ j < 3, ∀ l < 25, e.inp (58 + 25 * j + l) = (([a0, a1, a2].getD j #[]).toList.getD l 0).f₀ := by
    intro j hj l hl
    have hsz : ([a0, a1, a2].getD j #[]).size = m := by interval_cases j <;> assumption
    rw [hinp' _ (by omega)]
    simp only [rssLay, hM, show ¬ 58 + 25 * j + l < 8 by omega, show ¬ 58 + 25 * j + l < 58 by omega,
      show 58 + 25 * j + l < 133 by omega, ite_false, ite_true, show (58 + 25 * j + l - 58) % 25 = l by omega,
      show (58 + 25 * j + l - 58) / 25 = j by omega]
    by_cases hlm : l < m
    · simp only [hlm, ite_true, Option.map_some, Option.getD_some]
      rw [show 9 + 2 * m + 2 * m * j + 2 * l = 9 + 2 * m + 2 * m * j + 2 * l from rfl, hcl j hj _ (by omega),
        (encK_getD _ l).1]
    · simp only [hlm, ite_false, Option.map_none, Option.getD_none]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList, hsz]; omega)]; rfl
  -- the value
  have hT : kRSS.T cst = rsSegT cst := rfl
  rw [hT]
  refine GM.ok_mono (g := rsSegT cst) (ok_rsSegT h1 hcst) fun o ho _ => ?_
  rw [ho]
  rw [hp, flatMap_encV_k, implP1_rsWeight, hR]
  simp only [List.map_cons, List.map_nil]
  rw [hra, hκv, hρa, ha0, ha1, ha2, show (Val.af ra).toAF = ra from rfl, show (Val.f κv).toF = κv from rfl,
    show (Val.ak ρa).toAK = ρa from rfl, show (Val.ak a0).toAK = a0 from rfl, show (Val.ak a1).toAK = a1 from rfl,
    show (Val.ak a2).toAK = a2 from rfl]
  rw [rsWeightF_seg ra hrs a0 a1 a2 ρa m hm1 hm2 ha0s ha1s ha2s hρs (hfz 0 (by norm_num)) (hfz 1 (by norm_num))
    (hfz 2 (by norm_num)) κv]
  refine congrArg encK ?_
  refine rsSegV_congr _ _ _ _ _ _ _ _ ?_ hinκ ?_ ?_
  · refine List.ext_getElem (by simp [hrs]) fun p h1p h2p => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [hin7 p (by simpa using h1p), List.getD_eq_getElem _ _ h2p]
  · exact List.map_congr_left fun l hl => hinρ l (List.mem_range.1 hl)
  · exact fun j hj l hl => hina j hj l hl

/-! ## Prototype 1's templates -/


theorem rtC1d_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    (hS : SegBase impl₀) {π : ℕ} (hπ : π ≤ 1) (ι : Kind) :
    RTOkW (implP impl₀ base π ι) (Xof π) (rtC1d π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtC1c_ok hZ hB (π := 0) (by norm_num) ι
    simpa only [rtC1c, rtC1d, ite_true] using h0
  · obtain rfl : π = 1 := by omega
    simp only [rtC1d, one_ne_zero, ite_false, ite_true, rtSeg1]
    exact RT.orElse_okW (rtLinkSegW_ok base hZ repB ι)
      (RT.orElse_okW (rtEvZ_okW impl₀ base repB ι) (RT.orElse_okW (rtKD_okW repB cbRSS (kRSS_ok hS.1 ι))
        (RT.orElse_okW (rtKD_okW repB cbTSS (kTSS_ok ι)) (rtKD_okW repB cbSTS (kSTS_ok hS.2 ι)))))

/-- **`RepOkW` for `rtC1d`.** -/
theorem repOkW_rtC1d {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    (hS : SegBase impl₀) : RepOkW rtC1d impl₀ base := fun _ hπ ι => rtC1d_ok hZ hB hS hπ ι

/-- The certificate's base ops are a `SegBase`. -/
theorem segBase_implB : SegBase Sub4.implB := ⟨rfl, rfl⟩

/-- **`rtC1d` is sound at the certificate's ops.** -/
theorem repOkW_rtC1dB : RepOkW rtC1d Sub4.implB (fun _ => Sub4.implB) :=
  repOkW_rtC1d (fun _ _ => rfl) (fun _ => rfl) segBase_implB

/-! ## Controls -/

/-- (+) The segment's `rsWeight` shape is covered: `act` false, three claims. -/
theorem isRSS_pos : isRSS (.rsWeight 0 (fun _ => [1, 2, 3]) 4 5 (fun _ => false) 6) = true := by decide

/-- (−) … not with `act` true at some index (`β` would be read). -/
theorem isRSS_neg_act : isRSS (.rsWeight 0 (fun _ => [1, 2, 3]) 4 5 (fun ι => ι == .P30) 6) = false := by decide

/-- (−) … nor with two claims. -/
theorem isRSS_neg_claims : isRSS (.rsWeight 0 (fun _ => [1, 2]) 4 5 (fun _ => false) 6) = false := by decide

/-- (+) The three segment widths are served. -/
theorem rssIn_pos : ∀ m ∈ [23, 24, 25], rssIn [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] = true := by decide

/-- (−) … not 26 (the template has 25 coordinates), not 22 (`kwS_one` needs 16 block coordinates). -/
theorem rssIn_neg : rssIn [.af 7, .f, .f, .ak 26, .ak 26, .ak 26, .ak 26] = false ∧
    rssIn [.af 7, .f, .f, .ak 22, .ak 22, .ak 22, .ak 22] = false := by decide

/-- (−) … nor claims of another width than `ρ`, nor another `r″`. -/
theorem rssIn_neg' : rssIn [.af 7, .f, .f, .ak 25, .ak 24, .ak 25, .ak 25] = false ∧
    rssIn [.af 8, .f, .f, .ak 25, .ak 25, .ak 25, .ak 25] = false := by decide

/-- (+) The forced positions at `m = 23` are the claims' `f₁` (encoding offset `9 + 2·23` for the
claims, then `f₁` at odd offsets). -/
theorem rssZf_pos : rssZf [.af 7, .f, .f, .ak 23, .ak 23, .ak 23, .ak 23] =
    (List.range 3).flatMap fun j => (List.range 23).map fun l => 56 + 46 * j + 2 * l := by
  simp only [rssZf, rssM]

end N4s
end FR

end G6_FRNodeRows4RepSeg

section G6_FRNodeRows4RepF

-- New for `flock-recursive` (track REPF; C1-RESULT §5, C1b-RESULT §5): the replay part of `Gaps4`
-- discharged — the previous node's five ops and the segment's `linkWAll` are rows of `nodeIRows4`.

/-!
# The replay discharged

`nodeIRows4` folds `repIRowsW rtC1d` (`FRNodeRows4.repAllRows`, gated by `ArFit` and `RepFit`; SEG-R2: was
`rtC1c`), and
`RepOk`/`RepHolds`/`repIRows4` are the `RTOkW` forms (`FRNodeRows4Rep`; B3's `compileFromX_run` takes
the replay rows at an assignment agreeing with the slot's below `repB`). So the two replay hypotheses of
B3's/SRA's/ASK-T's/IMPC's `Gap4.imp` theorems hold at `rt := rtC1d` for the certificate's ops:

* **`repFit_of`**: the statement's rows give `ProtoFit`, `ArFit` and `RepFit` (else a rejecting row
  `one · one = 0` is a row of `nodeIRows4`);
* **`repFold`**: the replay fold `hfoldR` (every slot's `repIRows4 rtC1d` rows are rows of `nodeIRows4`);
* **`repOk_rtC1cB`**: `RepOk rtC1c implB (fun _ => implB)` (C1/R3/C1b's `repOkW_rtC1c` at `implB`);
  **`repOk_rtC1dB`**: the same for `rtC1d` (SEG-R1's `repOkW_rtC1dB`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-- **The fits from the statement's rows**: if the prototypes, the arenas or the replay rows did not
fit, `nodeIRows4` would hold a rejecting row. -/
theorem repFit_of {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ProtoFit ∧ ArFit ∧ RepFit := by
  have hF := protoFit_of hone hE
  have hA := arFit_of hone hE
  refine ⟨hF, hA, ?_⟩
  by_contra hR
  have hm : (repSegB, rejR κ) ∈ nodeIRows4 κ :=
    mem_node_rep hF (by rw [repAllRows, if_pos hA, if_neg hR]; exact List.mem_singleton_self _)
  have h := hE _ hm
  exact rejectRows_ctl κ w hone fun p hp => by
    simp only [rejectRows, List.mem_singleton] at hp; subst hp; exact h

/-- **The replay fold** (`hfoldR` of `gap4Imp_of_run`/`_rsv`/`_askT`/`_impc`/`_close` at `rt := rtC1d`). -/
theorem repFold {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ repIRows4 rtC1d κ v, p ∈ nodeIRows4 κ := by
  obtain ⟨hF, hA, hR⟩ := repFit_of hone hE
  intro v hv p hp
  exact mem_node_rep hF (by
    rw [repAllRows, if_pos hA, if_pos hR]
    exact List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, (repIRows4_eq rtC1d κ v) ▸ hp⟩)

/-- **The replay templates are sound at the certificate's ops** (`RepOk`, the `RTOkW` form). -/
theorem repOk_rtC1cB : RepOk rtC1c Sub4.implB (fun _ => Sub4.implB) :=
  repOk_iff.2 (repOkW_rtC1c (fun _ _ => rfl) (fun _ => rfl))

/-- **`rtC1d` is sound at the certificate's ops** (`RepOk` form; SEG-R2). -/
theorem repOk_rtC1dB : RepOk rtC1d Sub4.implB (fun _ => Sub4.implB) := repOk_iff.2 repOkW_rtC1dB

theorem implT_implB : ImplT Sub4.implB := by
  unfold Sub4.implB Impl.implCN
  exact Impl.implCWith_implT _ _

end N4s
end FR

end G6_FRNodeRows4RepF
