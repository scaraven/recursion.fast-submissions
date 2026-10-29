-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; track S-L4): the node decoder's
-- links on the accepted run's chain. 3.x analogue: `FRSoundnessExtLinks` (S-N1, `E_node`'s links).
import FRNodeLinks4
import FRXOut4

/-!
# The node decoder's links on the run's chain, and its read law

S-H4's decoder (`FRXOut4`) has the links **`LinksD4`** (`decF04_sem`'s hypotheses on the log and
the proof) and the witness **`readW4 sg`** (the statements from their cells, the signed children
of `rd4 pf4` with the signature read from H by `sg`). Both sides of `ReadIface4` at `rd4 pf4`:

* **`linksD4_of_run`**: on the run's chain (`RunLink4`, `AcceptTail`, a good log) `LinksD4` holds
  (3.x's `E_node_of_run` links at revision 4.1):

  | link | lemma |
  |---|---|
  | `¬ StateHit L` | `¬ Bad L` (`muT_lt_one`) |
  | `fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p)` | **`fmAns_of_run4`** (no repeated query; `vkOf_node4`) |
  | `capDig es i e = capPi4 i π e` | `capDig_eq4` (R4), `cap_lv_node` |
  | `finalAt es x = finPi4 π x` | `finalAt_eq4` (R4), `fin_lv_node` |
  | `¬ farL`, `consSet = jointAgree` | `tail_of_accept`'s `LigeritoOut.close`, `.agree` |

* **`readW4_law`**: `readW4 sg` meets the read law `ReadW4` at `rd4 pf4` if the H signature is L's
  on the node's statement (**`SigH4 sg`**, S-G/S-E's `sig_of_H`): `readW4_eq` with `wF = T4.fF`
  (`wF_eq_fF`).
* **`hL_of_sig`**: `hL` for a decoder with the links `LinksD4` and the witness `readW4 sg`, from
  `hRes` at `rd4 pf4` and `SigH4 sg`.
-/

namespace FR.Snd.L4
open RecursionFast Rev4 X4 R4 FR.X.X4

/-! ## Level parameters and `f⁽⁰⁾` -/

/-- **`FRXOut4`'s `wF` is the tail's `f⁽⁰⁾`** at a node kind (level 0 has 64 rows). -/
theorem wF_eq_fF (κ : NodeKind) (L es : Log) : X.wF κ L es = T4.fF (.node κ) L es := by
  have h : (CKind.lv (.node κ) 0).rows = 64 := by cases κ <;> decide
  funext e; simp only [X.wF, T4.fF, T4.fTab, h]

/-- A node kind's cap depths are `seq4`'s. -/
theorem cap_lv_node (κ : NodeKind) {i : ℕ} (hi : i < 5) : (CKind.lv (.node κ) i).cap = (seq4.lv i).cap := by
  interval_cases i <;> cases κ <;> decide

/-- A node kind's final message has at most `128` elements. -/
theorem fin_lv_node (κ : NodeKind) : 2 ^ T4.mLog (.node κ) 4 ≤ 128 := by
  cases κ <;> decide

/-! ## On the run's chain -/

section Run
variable {impl : OpImpl} {p : KindP} {vk c : Digest} {π : Proof} {tr : Trace}
  {y : List Val × List Bool × Trace}

/-- In a log without repeated queries, the first match of an entry's query is its answer. -/
theorem findSnd_of_mem4 {L : Log} (hL : (L.map Prod.fst).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : (L.find? fun x => decide (x.1 = e.1)).map Prod.snd = some e.2 := by
  rw [find_of_mem hL he]; rfl

/-- **The forward chain of first matches is the run's chain** (3.x's `fmAns_of_run` at `seq4`). -/
theorem fmAns_of_run4 (h : SkRun4 impl p ⟨vk, c, π⟩ tr y) {L : Log} (hb : ¬ Bad L)
    (hin : ∀ e ∈ tr, e ∈ L) (st₀ : Digest) :
    ∀ q < 482, X.fmAns (X.fsQ4 seq4 vk c π) st₀ L q = some (ansAt (fsOf tr (itemsOf seq4)) q) := by
  have hnd : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  have hlen := h.len
  have hmem : ∀ q < 482, (fsOf tr (itemsOf seq4)).getD q default ∈ L := fun q hq => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hin _ (mem_fsOf (List.getElem_mem _))
  intro q
  induction q with
  | zero =>
    intro _
    have hq : ((fsOf tr (itemsOf seq4)).getD 0 default).1 =
        X.fsQ4 seq4 vk c π 0 ((fsOf tr (itemsOf seq4)).getD (0 - 1) default).2 := h.hq 0 (by norm_num)
    have e0 : X.fsQ4 seq4 vk c π 0 st₀ =
        X.fsQ4 seq4 vk c π 0 ((fsOf tr (itemsOf seq4)).getD (0 - 1) default).2 := by
      simp only [X.fsQ4_zero]
    rw [X.fmAns, e0, ← hq]
    exact findSnd_of_mem4 hnd (hmem 0 (by norm_num))
  | succ q ih =>
    intro hq'
    rw [X.fmAns, ih (by omega), Option.bind_some]
    have hq : ((fsOf tr (itemsOf seq4)).getD (q + 1) default).1 =
        X.fsQ4 seq4 vk c π (q + 1) ((fsOf tr (itemsOf seq4)).getD (q + 1 - 1) default).2 := h.hq (q + 1) hq'
    rw [Nat.add_sub_cancel] at hq
    rw [show ansAt (fsOf tr (itemsOf seq4)) q = ((fsOf tr (itemsOf seq4)).getD q default).2 from rfl, ← hq]
    exact findSnd_of_mem4 hnd (hmem (q + 1) hq')

end Run

section C
variable (fin : Finals) (lRows : List Circ.Row) (κs₀ : F)

/-- **`LinksD4` holds on the accepted run's chain** (3.x's `E_node_of_run` links, at revision 4.1). -/
theorem linksD4_of_run {κ : NodeKind} {vk c : Digest} {π : Proof} {L : Log} {j : ℕ}
    (hG : GoodX P4f.DFhi L) (hR : RunLink4 fin lRows κs₀ κ vk c π L j)
    (hT : T4.AcceptTail RejFX W0X c0X L j) : X.LinksD4 κ L (entriesOf L (pathOf L j)) π c := by
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨tr, y, hS, hsem, hin, -, hes, -⟩ := hR
  have hvk : X.vkOf π = vk := vkOf_node4 (inp := ⟨vk, c, π⟩) hS
  have hkC : kindOfC (fsOf tr (itemsOf seq4)) = .node κ := kindOfC_acc_node hsem
  obtain ⟨-, hLig⟩ := T4.tail_of_accept (frontObl_X P4f.frontHi_X).loc (frontChainStab_X P4f.frontHi_X) hG.2 hT
  rw [hes] at hLig ⊢
  refine ⟨fun hs => hb (Or.inr (Or.inr (Or.inl hs))), ⟨zeroD, fun q hq => ?_⟩, fun i hi e he => ?_,
    fun x hx => ?_,
    fun i hi => by have h := hLig.close i hi; rwa [hkC] at h,
    fun i hi => by have h := hLig.agree i hi; rwa [hkC] at h⟩
  · rw [hvk]; exact fmAns_of_run4 hS hb hin zeroD q (by unfold X.nRep4 at hq; omega)
  · rw [cap_lv_node κ hi] at he
    exact capDig_eq4 hS hi he
  · exact finalAt_eq4 hS (lt_of_lt_of_le hx (fin_lv_node κ))

/-- **`ReadIface4` for a decoder whose links follow from `LinksD4`** and which meets the read law. -/
theorem readIface4_of {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (rd : N4c.Read4) (vk : Digest)
    (hW : ReadW4 D.readW rd vk) : ReadIface4 fin lRows κs₀ D rd vk :=
  ⟨fun κ L c π _j hG _ _ hR hT => hLk κ L _ π c (linksD4_of_run fin lRows κs₀ hG hR hT), hW⟩

/-! ## The read law of `readW4` -/

/-- **The H side's signature is L's** on the node's statement (S-G/S-E's `sig_of_H`): on every
`f⁽⁰⁾` meeting `StmtN4`, the decoder's signature reader `sg` reads what `rd4`'s `readSig4` reads. -/
def SigH4 (sg : NodeKind → ℕ → Circ.Asg → Sig) (vk : Digest) : Prop :=
  ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → ∀ σ < 2, sg κ σ w = N4s.readSig4 κ σ w

/-- **`readW4 sg` meets the read law at `rd4 pf4`** given `SigH4 sg` (`readW4_eq`). -/
theorem readW4_law {sg : NodeKind → ℕ → Circ.Asg → Sig} {vk : Digest} (h : SigH4 sg vk) :
    ReadW4 (X.readW4 sg) (N4s.rd4 X.pf4) vk := by
  intro κ L es c₁ c₂ hS
  rw [← wF_eq_fF] at hS ⊢
  exact X.readW4_eq hS.2.2.2.2 (h κ _ c₁ c₂ hS)

/-- **`hL` for S-H4's decoder** (links `LinksD4`, witness `readW4 sg`): from the residual `hRes` at
`rd4 pf4` and `SigH4 sg`. -/
theorem hL_of_sig (S : Submission) (vk : Digest)
    (hV : S.V = VC4 (Impl.implC fin lRows κs₀) (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4)
    (hq : S.qV = qV4) {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg) (hsig : SigH4 sg vk)
    (I : N4c.SlotIface4 (VsegC (Impl.implC fin lRows κs₀))
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4))
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I (N4s.rd4 X.pf4) κ vk c₁ c₂ w) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F fun _ => Impl.implC fin lRows κs₀) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es) :=
  hL_of_res fin lRows κs₀ S vk hV hq D I _ hI hRes
    (readIface4_of fin lRows κs₀ D hLk _ vk (hW ▸ readW4_law hsig))

end C

/-! ## Controls -/

/-- (−) **`LinksD4` fails on a log with a state hit** (its first conjunct). -/
theorem linksD4_stateHit {κ : NodeKind} {L es : Log} {π : Proof} {c : Digest} (h : StateHit L) :
    ¬ X.LinksD4 κ L es π c := fun hl => hl.1 h

/-- (+) **`SigH4` holds for L's own reader** `readSig4` (the decoder cannot use it: L's row 0 is
not decoded, `out_cells_rows`). -/
theorem sigH4_readSig4 (vk : Digest) : SigH4 N4s.readSig4 vk := fun _ _ _ _ _ _ _ => rfl

/-- (−) **`SigH4` has content**: a reader that differs from `readSig4` on some statement-meeting
witness fails it. -/
theorem sigH4_ne {sg : NodeKind → ℕ → Circ.Asg → Sig} {vk : Digest} {κ : NodeKind} {w : Circ.Asg}
    {c₁ c₂ : Digest} (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) {σ : ℕ} (hσ : σ < 2)
    (hne : sg κ σ w ≠ N4s.readSig4 κ σ w) : ¬ SigH4 sg vk := fun h => hne (h κ w c₁ c₂ hS σ hσ)

/-- (value) The cap depths and the final message's size per node kind. -/
theorem lv_node_ctl : (CKind.lv (.node .N2) 0).cap = 9 ∧ 2 ^ T4.mLog (.node .N2) 4 = 64 ∧
    2 ^ T4.mLog (.node .N4) 4 = 128 := by decide

end FR.Snd.L4
