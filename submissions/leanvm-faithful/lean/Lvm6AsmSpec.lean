-- New for lvm6 (WP ASM): the composed whole-program specification of `prog6` from the phase
-- specifications (season 1's sequential composition `Spec.bind`, frame `Spec.frame`), its
-- certificate (F1's `kcert6`, `sound6`) and the refinement of V1's executable front.
import Lvm6AsmRing
import Lvm6FSCert

/-!
# The composed specification of `prog6`

BLUEPRINT v3 §5 (T2–T5, T7). The phases' specifications are WP S's frozen `Prop`s, taken as
hypotheses where a phase is still being proved:

* `Stmt.commitSpec6 I Φ.commit` (T3a: pinned, one commitment, `Tied c₀`), `Stmt.treeSpec Φ.tree`
  (T2), **`Stmt.spongeSpec6`** (new here: the sponge batch in the same `DoomSpec` shape, relation
  `SGood`), `Stmt.typedSpecE Φ.typed TGood` (T4, typed phases and mini-bus), `Stmt.ringSpec6 Φ.ring`
  (T4', list form), `Stmt.openSpec6 I Φ.whir` (T3), `Stmt.noCommit` of the tree, sponge, typed and
  ring programs, and `(I sh).L₀ ≤ sh.L₀` (`CAND-decision.md`).

**`spec6`**: from the empty history, `prog6 Φ sh vk x` accepts only on histories where some candidate
the pinned history binds satisfies the good relation `GoodAll` (`TreeOkAt ∧ SGood ∧ TGood` for the
header view), every group's escape at most `εI`, lead `0`. Proof (`CAND-decision.md` §4): after the
commitment, either a candidate is good already (`ExtAll` holds and is kept: `extSpec`), or none is:
then the doom transfers of tree → sponge → typed run on `cands`, framed with `JT c₀` (pinned, one
commitment, `Tied c₀`; kept by `noCommit`), `doomed_ball` moves doom to the list with claim 0,
`batchJ` runs the ring phase on `ball` (framed with pinned and the commitment count), and the
opening rejects from one commitment and doom over `ball` (`doomChain`).

**`spec6G`** (W2, RG): the same with `RG` in the postcondition, run in the `ExtAll` branch by
`extChainG`: the ring phase's unconditional batching fact (`ringSpecU`, from `Stmt.ringSpec6` at its
own count: the batched claim is multiaffine and, by claim 0 and `Tied c₀`, every list member
satisfying it is a candidate) and the opening's facts `GWc sh cl` for that claim
(`Stmt.openGoodC`); `SI6G`, `kcertAsmG`, `sound_asmG` with `Ext = ExtAll ∧ RG I GWc P18`.
**`SI6`** is `kcert6`'s hypothesis `SI` for `schemeOf prog6`; **`sound_asm`** is WP S's
`Open6.sound` from the phase statements, the extractor's obligations (`Ext6`, X2) and `ExtEq6`.
**`refines6_asm`**: V1's front `VS6` with the decision `F6 := replay prog6` refines
`schemeOf prog6` (`VS6_refines` and `replay_refines`), so `Stmt.refines6 (VSasm Φ) (prog6 Φ)`.
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.Compile Lvm.FS RecursionFast Lvm.T
open LeanVM.Protocol.EndToEnd.Front (Doomed)
open scoped ENNReal NNReal

/-! ## A trivial specification -/

/-- Any program, doom everywhere, potential `0`: the specification that carries a framed
invariant and nothing else. -/
def specTriv {α : Type} (p : VerifierProgram α) {εmax : ℝ≥0∞} :
    Spec p (fun _ ↦ True) (fun _ _ ↦ True) εmax 0 0 where
  D _ _ := True
  V _ _ := 0
  le_one _ _ := zero_le_one
  start_D _ _ := trivial
  start_V _ _ := le_rfl
  read _ _ _ _ := trivial
  grind _ _ _ := trivial
  commit _ _ _ _ _ := trivial
  sample _ _ := by simp
  query _ _ _ := le_rfl
  moveEnd _ _ _ hD := (hD trivial).elim
  retEnd _ _ hD := (hD trivial).elim
  retDoom _ _ _ := by simp
  post _ _ _ := trivial
  bound _ _ _ _ := by simp

/-! ## The new phase statement and the good relation -/

/-- **The sponge batch's doom transfer** (§6.3, same shape as `Stmt.treeSpec`): from the sponge
relation `SGood x` (CB's `SpongeClaims`/`OutRel` placed on the stack, CD) to its slice and stack
claims. -/
def Stmt.spongeSpec6 (spongeProg : Shape → Hdr → VerifierProgram TreeOut)
    (SGood : Hdr → Stack → Prop) : Prop :=
  ∀ sh x, DoomSpec (spongeProg sh x) (SGood x) (fun o q ↦ o.Holds sh.M q)

/-- **The good relation** of a header view: the tree relation for its root, the sponge's, the
typed phases'. -/
def GoodAll (SGood TGood : Hdr → Stack → Prop) (sh : Shape) (x : Hdr) (q : Stack) : Prop :=
  TreeOkAt sh.logN q x.h ∧ SGood x q ∧ TGood x q

/-- **What an accepting history gives the extractor**: it is pinned and one of its candidates is
good for the header's view. -/
def ExtAll (I : Shape → OpeningIface) (SGood TGood : Hdr → Stack → Prop) (sh : Shape)
    (x : List UInt8) (h : List Ev) : Prop :=
  (I sh).pinned h ∧ ∃ q ∈ (I sh).cands h, GoodAll SGood TGood sh (hdrView sh x) q

/-- **Claim 0 is multiaffine** (W1 F-3; WP MA's `commit6_ma`): every claim the commitment
returns (`RetAll`, WP MA's `Lvm6MultiaffBase`). -/
def Stmt.commitMA (commitProg : Shape → VerifierProgram StackClaim6) : Prop :=
  ∀ sh, RetAll (fun c0 : StackClaim6 ↦ c0.Multiaffine sh.M) (commitProg sh)

/-- **The tree's stack claims are multiaffine** (WP MA's `treeProgS6_ma`). -/
def Stmt.treeMA (treeProg : Shape → Hdr → VerifierProgram TreeOut) : Prop :=
  ∀ sh x, RetAll (fun o : TreeOut ↦ ∀ c ∈ o.claims, c.Multiaffine sh.M) (treeProg sh x)

/-- **The sponge's stack claims are multiaffine** (WP MA, once SPH's sponge phase exists). -/
def Stmt.spongeMA (spongeProg : Shape → Hdr → VerifierProgram TreeOut) : Prop :=
  ∀ sh x, RetAll (fun o : TreeOut ↦ ∀ c ∈ o.claims, c.Multiaffine sh.M) (spongeProg sh x)

/-- **The typed phases' stack claims are multiaffine** (WP MA's `typedPhase6_ma_at`). -/
def Stmt.typedMA (typedProg : Shape → Hdr → VerifierProgram (List StackClaim6)) : Prop :=
  ∀ sh x, RetAll (fun ty : List StackClaim6 ↦ ∀ c ∈ ty, c.Multiaffine sh.M) (typedProg sh x)

/-- The phase statements `spec6` assembles (`CAND-decision.md`). -/
structure PhaseSpecs (Φ : Phases) (I : Shape → OpeningIface) (SGood TGood : Hdr → Stack → Prop) :
    Prop where
  commit : Stmt.commitSpec6 I Φ.commit
  tree : Stmt.treeSpec Φ.tree
  sponge : Stmt.spongeSpec6 Φ.sponge SGood
  typed : Stmt.typedSpecE Φ.typed TGood
  ring : Stmt.ringSpec6 Φ.ring
  opening : Stmt.openSpec6 I Φ.whir
  /-- The list bound of the opening's interface is the shape's. -/
  listL : ∀ sh, (I sh).L₀ ≤ sh.L₀
  /-- The phases between the commitment and the opening commit nothing (K1, CB, Y1/MB; RS's:
  `ringPhase6_noCommit`). -/
  ncTree : ∀ sh x, Stmt.noCommit (Φ.tree sh x)
  ncSponge : ∀ sh x, Stmt.noCommit (Φ.sponge sh x)
  ncTyped : ∀ sh x, Stmt.noCommit (Φ.typed sh x)
  ncRing : ∀ sh sl st, Stmt.noCommit (Φ.ring sh sl st)
  /-- The claims the phases return are multiaffine (W1 F-3, `ringSpec6`'s hypothesis; WP MA:
  `commit6_ma`, `treeProgS6_ma`, `typedPhase6_ma_at`; the sponge's waits for SPH). -/
  maCommit : Stmt.commitMA Φ.commit
  maTree : Stmt.treeMA Φ.tree
  maSponge : Stmt.spongeMA Φ.sponge
  maTyped : Stmt.typedMA Φ.typed

/-- The list `ringSpec6` receives is multiaffine when each phase's claims are (WP MA). -/
theorem stackedOf_ma {μ : ℕ} {c0 : StackClaim6} {t s : TreeOut} {ty : List StackClaim6}
    (h0 : c0.Multiaffine μ) (ht : ∀ c ∈ t.claims, c.Multiaffine μ)
    (hs : ∀ c ∈ s.claims, c.Multiaffine μ) (hty : ∀ c ∈ ty, c.Multiaffine μ) :
    ∀ c ∈ stackedOf c0 t s ty, c.Multiaffine μ := by
  intro c hc
  simp only [stackedOf, List.mem_cons, List.mem_append] at hc
  rcases hc with rfl | hc | hc | hc
  · exact h0
  · exact ht c hc
  · exact hs c hc
  · exact hty c hc

section Chain

variable {Φ : Phases} {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
  (H : PhaseSpecs Φ I SGood TGood) (sh : Shape)

/-- What the commitment establishes and every later phase keeps: pinned, one commitment, `Tied c₀`. -/
def JT (I : Shape → OpeningIface) (sh : Shape) (c0 : StackClaim6) (h : List Ev) : Prop :=
  (I sh).pinned h ∧ (commits h).length = 1 ∧ (I sh).Tied sh.M c0 h

theorem jt_append {c0 : StackClaim6} {h₀ l : List Ev} (hl : commits l = []) (h : JT I sh c0 h₀) :
    JT I sh c0 (h₀ ++ l) :=
  ⟨(I sh).pinned_append h₀ l h.1,
    (by rw [VerifierProgram.commits_app, hl, List.append_nil]; exact h.2.1),
    OpeningIface.Tied.append l h.1 h.2.2⟩

/-- A phase's doom transfer on the candidates, framed with `JT c₀`. -/
noncomputable def phaseSpec {α : Type} {p : VerifierProgram α} {Good : Stack → Prop}
    {Holds : α → Stack → Prop} (hD : DoomSpec p Good Holds) (hnc : Stmt.noCommit p)
    (c0 : StackClaim6) (R : Stack → Prop) :
    Spec p (fun h ↦ JT I sh c0 h ∧ Doomed (I sh).cands (fun q ↦ Good q ∧ R q) h)
      (fun out h ↦ Doomed (I sh).cands (fun q ↦ Holds out q ∧ R q) h ∧ JT I sh c0 h) εI 0 0 :=
  ((hD (I sh).cands R (I sh).pinned (I sh).cands_append (I sh).pinned_sub).some.frame (JT I sh c0)
    (fun h₀ l hr hj ↦ jt_append sh (hnc h₀ l hr) hj)).mono (fun _ hp ↦ ⟨⟨hp.1.1, hp.2⟩, hp.1⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- `batchJ`: the `J₀` check, then the ring phase on the list (at most two slice sets), framed with
the pin and the commitment count. -/
noncomputable def batchSpec (sl : List SliceClaim) (st : List StackClaim6) (hsl : sl.length ≤ 2)
    (hma : ∀ c ∈ st, c.Multiaffine sh.M) :
    Spec (batchJ Φ sh sl st)
      (fun h ↦ ((I sh).pinned h ∧ (commits h).length = 1) ∧ Doomed (I sh).ball
        (fun q ↦ (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q) h)
      (fun cl h ↦ (cl.Multiaffine sh.M ∧ Doomed (I sh).ball (fun q ↦ cl.Holds sh.M q) h) ∧
        ((I sh).pinned h ∧ (commits h).length = 1)) εI 0 0 :=
  (Spec.require (c := sl.length + st.length ≤ sh.J₀) (Post := fun _ h ↦ (((I sh).pinned h ∧
      (commits h).length = 1) ∧ Doomed (I sh).ball
        (fun q ↦ (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q) h) ∧
      sl.length + st.length ≤ sh.J₀) fun _ hp hc ↦ ⟨hp, hc⟩).bind' fun _ ↦
    if hc : sl.length + st.length ≤ sh.J₀ then
      ((H.ring sh sl st hsl hc hma (I sh).ball (I sh).pinned (I sh).ball_append fun h hp ↦
          ⟨((I sh).ball_card h hp).1, ((I sh).ball_card h hp).2.trans (H.listL sh)⟩).some.frame
        (fun h ↦ (I sh).pinned h ∧ (commits h).length = 1) (fun h₀ l hr hj ↦
          ⟨(I sh).pinned_append h₀ l hj.1, by
            rw [VerifierProgram.commits_app, H.ncRing sh sl st h₀ l hr, List.append_nil]
            exact hj.2⟩)).mono
        (fun _ hp ↦ ⟨⟨hp.1.1.1, hp.1.2⟩, hp.1.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hc hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **No candidate good ⟹ rejection**: tree, sponge, typed phases on `cands`, `doomed_ball`,
`batchJ` and the opening on `ball`; each phase's claims are multiaffine (`Spec.retInv` with
`PhaseSpecs.ma*`), as `ringSpec6` and the opening ask. -/
noncomputable def doomChain (x : Hdr) (c0 : StackClaim6) (h0 : c0.Multiaffine sh.M) :
    Spec (rest6 Φ sh x c0)
      (fun h ↦ JT I sh c0 h ∧ Doomed (I sh).cands (fun q ↦ TreeOkAt sh.logN q x.h ∧
        SGood x q ∧ TGood x q) h) (fun b _ ↦ b = false) εI 0 0 :=
  ((phaseSpec sh (H.tree sh x) (H.ncTree sh x) c0 (fun q ↦ SGood x q ∧ TGood x q)).retInv
    (fun t ↦ ∀ c ∈ t.claims, c.Multiaffine sh.M) (H.maTree sh x).ret).bind' fun t ↦
  if ht : ∀ c ∈ t.claims, c.Multiaffine sh.M then
  (((phaseSpec sh (H.sponge sh x) (H.ncSponge sh x) c0
    (fun q ↦ t.Holds sh.M q ∧ TGood x q)).retInv
    (fun s ↦ ∀ c ∈ s.claims, c.Multiaffine sh.M) (H.maSponge sh x).ret).mono
    (fun _ hp ↦ ⟨hp.1.2, hp.1.1.mono fun _ hq ↦ ⟨hq.2.1, hq.1, hq.2.2⟩⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun s ↦
  if hs : ∀ c ∈ s.claims, c.Multiaffine sh.M then
  (((phaseSpec sh (H.typed sh x) (H.ncTyped sh x) c0
    (fun q ↦ s.Holds sh.M q ∧ t.Holds sh.M q)).retInv
    (fun ty ↦ ∀ c ∈ ty, c.Multiaffine sh.M) (H.maTyped sh x).ret).mono
    (fun _ hp ↦ ⟨hp.1.2, hp.1.1.mono fun _ hq ↦ ⟨hq.2.1, hq.2.2, hq.1⟩⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ty ↦
  if hty : ∀ c ∈ ty, c.Multiaffine sh.M then
  ((batchSpec H sh [t.slices, s.slices] (stackedOf c0 t s ty) (by simp)
      (stackedOf_ma h0 ht hs hty)).mono
    (fun _ hp ↦ ⟨⟨hp.1.2.1, hp.1.2.2.1⟩, (OpeningIface.doomed_ball hp.1.2.2.2 hp.1.1).mono
      fun q hq ↦ by
      obtain ⟨hsl, hst⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsl
      simp only [stackedOf, List.mem_cons, List.mem_append, forall_eq_or_imp] at hst
      exact ⟨hst.1, fun c hc ↦ hst.2 c (Or.inr (Or.inr hc)), ⟨hsl.2, fun c hc ↦ hst.2 c (Or.inr
        (Or.inl hc))⟩, ⟨hsl.1, fun c hc ↦ hst.2 c (Or.inl hc)⟩⟩⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun cl ↦
  if hcl : cl.Multiaffine sh.M then
    (H.opening sh cl hcl).some.mono (fun _ hp ↦ ⟨hp.2.2, hp.1.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  else Spec.dead.mono (fun _ hp ↦ hcl hp.1.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hty hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hs hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ ht hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

theorem extAll_append (x : List UInt8) (h₀ l : List Ev) (h : ExtAll I SGood TGood sh x h₀) :
    ExtAll I SGood TGood sh x (h₀ ++ l) :=
  ⟨(I sh).pinned_append h₀ l h.1, by rw [(I sh).cands_append h₀ l h.1]; exact h.2⟩

/-- **A good candidate stays**: any program keeps `ExtAll`. -/
noncomputable def extSpec {α : Type} (p : VerifierProgram α) (x : List UInt8) :
    Spec p (ExtAll I SGood TGood sh x) (fun _ h ↦ ExtAll I SGood TGood sh x h) εI 0 0 :=
  ((specTriv p).frame (ExtAll I SGood TGood sh x) fun h₀ l _ h ↦ extAll_append sh x h₀ l h).mono
    (fun _ h ↦ ⟨trivial, h⟩) (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl

/-- The two cases after the commitment. -/
def casePre (A B : List Ev → Prop) : Bool → List Ev → Prop
  | true => A
  | false => B

/-- **After the commitment**: a good candidate already, or doom of the good relation. -/
noncomputable def restSpec (x : List UInt8) (c0 : StackClaim6) (h0 : c0.Multiaffine sh.M) :
    Spec (rest6 Φ sh (hdrView sh x) c0)
      (fun h ↦ (I sh).pinned h ∧ (commits h).length = 1 ∧ (I sh).Tied sh.M c0 h)
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h) εI 0 0 := by
  classical
  refine (Spec.exPre (ι := Bool) (Pre := casePre (ExtAll I SGood TGood sh x)
    (fun h ↦ JT I sh c0 h ∧ Doomed (I sh).cands (fun q ↦ GoodAll SGood TGood sh
      (hdrView sh x) q) h)) fun i ↦ ?_).mono (fun h hp ↦ ?_) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · cases i
    · exact (doomChain H sh (hdrView sh x) c0 h0).mono (fun _ h ↦ h) (fun b _ hb hb' ↦ by
        simp [hb] at hb') le_rfl le_rfl le_rfl
    · exact (extSpec sh _ x).mono (fun _ h ↦ h) (fun _ _ h _ ↦ h) le_rfl le_rfl le_rfl
  · by_cases he : ExtAll I SGood TGood sh x h
    · exact ⟨true, he⟩
    · exact ⟨false, hp, fun q hq hg ↦ he ⟨hp.1, q, hq, hg⟩⟩

open Classical in
/-- **The composed specification of `prog6`** (T2–T4' assembled into `kcert6`'s shape). -/
noncomputable def spec6 (vk : Digest) (x : List UInt8) :
    Spec (prog6 Φ sh vk x) (fun h ↦ h = []) (fun b h ↦ b = true → ExtAll I SGood TGood sh x h)
      εI 0 0 :=
  ((H.commit sh).some.retInv (fun c0 ↦ c0.Multiaffine sh.M) (H.maCommit sh).ret).bind' fun c0 ↦
    if h0 : c0.Multiaffine sh.M then
      (restSpec H sh x c0 h0).mono (fun _ hp ↦ hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ h0 hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Chain

/-! ## The extractor's conjunct outside the doom (W2; X6b F-X6b-2/F-X6b-3)

The extractor (X5's `SFront6.goodL`) needs facts about the opening's challenges on every accepting
available log: every fold pair outside the MCA exceptional set of its word, the claim back through every
fold, the level transitions' agreement. An accepting available log runs the `ExtAll` branch of
`restSpec` (the doom branch rejects), where `extSpec` carried nothing about the opening. `spec6G` runs
the opening's unconditional specification there (`Stmt.openGood6`, no doom precondition), so `kcert6`'s
`Ext` is `ExtAll ∧ GW`. The doom branch and every group's escape are `spec6`'s. -/

/-- **T3 with the extractor's facts** (W1/W2): from one commitment, the opening accepts only on
histories where `GW sh` holds, each group's escape at most `εI`; no doom precondition. -/
def Stmt.openGood6 (GW : Shape → List Ev → Prop)
    (whirProg : Shape → StackClaim6 → VerifierProgram Bool) : Prop :=
  ∀ sh cl, Nonempty (Spec (whirProg sh cl) (fun h ↦ (commits h).length = 1)
    (fun b h ↦ b = true → GW sh h) εI 0 0)

/-- **T3 with the extractor's facts, indexed by the opening's claim** (RG): `Stmt.openGood6` whose
facts may name the claim `cl` the opening was run on, so the extractor can match them with the ring
phase's output. W1's `openGood_W1` proves it for `GW18c sh cl h` (`GW18` with the existential `cl`
replaced by the parameter: its proof's witness is already `cl`). -/
def Stmt.openGoodC (GWc : Shape → StackClaim6 → List Ev → Prop)
    (whirProg : Shape → StackClaim6 → VerifierProgram Bool) : Prop :=
  ∀ sh cl, Nonempty (Spec (whirProg sh cl) (fun h ↦ (commits h).length = 1)
    (fun b h ↦ b = true → GWc sh cl h) εI 0 0)

/-- A claim-free `Stmt.openGood6` is a `Stmt.openGoodC`. -/
theorem Stmt.openGoodC_of {GW : Shape → List Ev → Prop}
    {whirProg : Shape → StackClaim6 → VerifierProgram Bool} (HG : Stmt.openGood6 GW whirProg) :
    Stmt.openGoodC (fun sh _ h ↦ GW sh h) whirProg := HG

/-! ### RG: the ring phase's unconditional batching fact (W1 F-W2-4) -/

open Classical in
/-- **The ring phase without doom** (RG's ring step; from `Stmt.ringSpec6` alone, same group, same
escape): on any history set `C` stable under `G` with at most `L₀` members, the batched claim is
multiaffine and every member of `C` that satisfies it satisfies every slice and stacked claim. Proof:
`Stmt.ringSpec6` at the members of `C` that fail some input claim (a subset, so stable and at most
`L₀`; doomed by definition). For `ringPhase6` the count is `ringSpec6_asm`'s: `card_bad6_le` per
member (`(|st| + 3)·|E2|^32` bad draws), `≤ εI` at `L₀` by `errG_le_εI`. -/
noncomputable def ringSpecU {ringProg : Shape → List SliceClaim → List StackClaim6 →
      VerifierProgram StackClaim6} (HR : Stmt.ringSpec6 ringProg) (sh : Shape) (sl : List SliceClaim)
    (st : List StackClaim6) (hsl : sl.length ≤ 2) (hc : sl.length + st.length ≤ sh.J₀)
    (hma : ∀ c ∈ st, c.Multiaffine sh.M) (C : List Ev → Set Stack) (G : List Ev → Prop)
    (hC : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀) (hcard : ∀ h, G h → (C h).Finite ∧ (C h).ncard ≤ sh.L₀) :
    Spec (ringProg sh sl st) G (fun out h ↦ out.Multiaffine sh.M ∧ ∀ q ∈ C h, out.Holds sh.M q →
      (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q) εI 0 0 :=
  (HR sh sl st hsl hc hma
    (fun h ↦ {q | q ∈ C h ∧ ¬ ((∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q)}) G
    (fun h₀ l hg ↦ by simp only [hC h₀ l hg])
    (fun h hg ↦ ⟨(hcard h hg).1.subset fun _ hq ↦ hq.1,
      (Set.ncard_le_ncard (fun _ hq ↦ hq.1) (hcard h hg).1).trans (hcard h hg).2⟩)).some.mono
    (fun _ hg ↦ ⟨hg, fun _ hq ↦ hq.2⟩)
    (fun _ _ hp ↦ ⟨hp.1, fun q hq ho ↦ by_contra fun hn ↦ hp.2 q ⟨hq, hn⟩ ho⟩) le_rfl le_rfl le_rfl

/-- **RG for the deployed ring phase** (`ringPhase6`, §6.5 at v2.4): `ringSpecU` at
`ringSpec6_asm`. -/
noncomputable def ringPhase6U (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6)
    (hsl : sl.length ≤ 2) (hc : sl.length + st.length ≤ sh.J₀) (hma : ∀ c ∈ st, c.Multiaffine sh.M)
    (C : List Ev → Set Stack) (G : List Ev → Prop) (hC : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hcard : ∀ h, G h → (C h).Finite ∧ (C h).ncard ≤ sh.L₀) :
    Spec (ringPhase6 sh sl st) G (fun out h ↦ out.Multiaffine sh.M ∧ ∀ q ∈ C h, out.Holds sh.M q →
      (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q) εI 0 0 :=
  ringSpecU ringSpec6_asm sh sl st hsl hc hma C G hC hcard

/-- **The batching tie**: every list member that satisfies `cl` is a candidate (with `Tied c₀`, from
claim 0 of the batch). -/
def BatchTie (I : Shape → OpeningIface) (sh : Shape) (cl : StackClaim6) (h : List Ev) : Prop :=
  ∀ q ∈ (I sh).ball h, cl.Holds sh.M q → q ∈ (I sh).cands h

/-- **RG**: the opening ran on a multiaffine claim `cl` tied to the candidates, and its facts
`GWc sh cl` hold. -/
def RG (I : Shape → OpeningIface) (GWc : Shape → StackClaim6 → List Ev → Prop) (sh : Shape)
    (h : List Ev) : Prop :=
  ∃ cl : StackClaim6, cl.Multiaffine sh.M ∧ BatchTie I sh cl h ∧ GWc sh cl h

theorem batchTie_append {I : Shape → OpeningIface} {sh : Shape} {cl : StackClaim6} {h₀ : List Ev}
    (l : List Ev) (hp : (I sh).pinned h₀) (ht : BatchTie I sh cl h₀) : BatchTie I sh cl (h₀ ++ l) := by
  intro q hq hcl
  rw [(I sh).cands_append h₀ l hp]
  exact ht q (by rwa [(I sh).ball_append h₀ l hp] at hq) hcl

/-- What `descends` uses: a list member satisfying the opening's claim is the pinned candidate. -/
theorem RG.mem_cands {I : Shape → OpeningIface} {GWc : Shape → StackClaim6 → List Ev → Prop}
    {sh : Shape} {h : List Ev} (hr : RG I GWc sh h) :
    ∃ cl : StackClaim6, cl.Multiaffine sh.M ∧ GWc sh cl h ∧
      ∀ q ∈ (I sh).ball h, cl.Holds sh.M q → q ∈ (I sh).cands h :=
  let ⟨cl, hm, ht, hg⟩ := hr; ⟨cl, hm, hg, ht⟩

section ChainG

variable {Φ : Phases} {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
  (H : PhaseSpecs Φ I SGood TGood) {GWc : Shape → StackClaim6 → List Ev → Prop}
  (HG : Stmt.openGoodC GWc Φ.whir) (sh : Shape)

/-- The `ExtAll` branch's frame: a good candidate and one commitment. -/
def ExtC (I : Shape → OpeningIface) (SGood TGood : Hdr → Stack → Prop) (sh : Shape) (x : List UInt8)
    (h : List Ev) : Prop :=
  ExtAll I SGood TGood sh x h ∧ (commits h).length = 1

theorem extC_append (x : List UInt8) {h₀ l : List Ev} (hl : commits l = [])
    (h : ExtC I SGood TGood sh x h₀) : ExtC I SGood TGood sh x (h₀ ++ l) :=
  ⟨extAll_append sh x h₀ l h.1, by rw [VerifierProgram.commits_app, hl, List.append_nil]; exact h.2⟩

/-- `ExtC` with claim 0 tied to the candidates (RG). -/
def ExtT (I : Shape → OpeningIface) (SGood TGood : Hdr → Stack → Prop) (sh : Shape) (x : List UInt8)
    (c0 : StackClaim6) (h : List Ev) : Prop :=
  ExtC I SGood TGood sh x h ∧ (I sh).Tied sh.M c0 h

theorem extT_append (x : List UInt8) (c0 : StackClaim6) {h₀ l : List Ev} (hl : commits l = [])
    (h : ExtT I SGood TGood sh x c0 h₀) : ExtT I SGood TGood sh x c0 (h₀ ++ l) :=
  ⟨extC_append sh x hl h.1, OpeningIface.Tied.append l h.1.1.1 h.2⟩

/-- A phase that commits nothing keeps `ExtT`. -/
noncomputable def extTSpec {α : Type} (p : VerifierProgram α) (hnc : Stmt.noCommit p) (x : List UInt8)
    (c0 : StackClaim6) :
    Spec p (ExtT I SGood TGood sh x c0) (fun _ h ↦ ExtT I SGood TGood sh x c0 h) εI 0 0 :=
  ((specTriv p).frame (ExtT I SGood TGood sh x c0) fun h₀ l hr h ↦
    extT_append sh x c0 (hnc h₀ l hr) h).mono
    (fun _ h ↦ ⟨trivial, h⟩) (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl

open Classical in
/-- **The `ExtAll` branch with the opening's and the ring's facts**: the phases keep `ExtT` (their
claims multiaffine by `PhaseSpecs.ma*`), the ring phase runs `ringSpecU` on `ball` (claim 0 is the
head of the stack list, so with `Tied c₀` the batched claim is tied to `cands`), and the opening's
`Stmt.openGoodC` adds `GWc sh cl` for that same `cl`. -/
noncomputable def extChainG (x : List UInt8) (c0 : StackClaim6) (h0 : c0.Multiaffine sh.M) :
    Spec (rest6 Φ sh (hdrView sh x) c0) (ExtT I SGood TGood sh x c0)
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h ∧ RG I GWc sh h) εI 0 0 :=
  ((extTSpec sh (Φ.tree sh (hdrView sh x)) (H.ncTree sh _) x c0).retInv
    (fun t ↦ ∀ c ∈ t.claims, c.Multiaffine sh.M) (H.maTree sh _).ret).bind' fun t ↦
  if ht : ∀ c ∈ t.claims, c.Multiaffine sh.M then
  (((extTSpec sh (Φ.sponge sh (hdrView sh x)) (H.ncSponge sh _) x c0).retInv
    (fun s ↦ ∀ c ∈ s.claims, c.Multiaffine sh.M) (H.maSponge sh _).ret).mono
    (fun _ hp ↦ hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun s ↦
  if hs : ∀ c ∈ s.claims, c.Multiaffine sh.M then
  (((extTSpec sh (Φ.typed sh (hdrView sh x)) (H.ncTyped sh _) x c0).retInv
    (fun ty ↦ ∀ c ∈ ty, c.Multiaffine sh.M) (H.maTyped sh _).ret).mono
    (fun _ hp ↦ hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ty ↦
  if hty : ∀ c ∈ ty, c.Multiaffine sh.M then
  ((Spec.require (c := [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ sh.J₀)
      (Post := fun _ h ↦ ExtT I SGood TGood sh x c0 h ∧
        [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ sh.J₀)
      fun _ hp hc ↦ ⟨hp.1, hc⟩).bind' fun _ ↦
    if hc : [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ sh.J₀ then
      ((ringSpecU H.ring sh [t.slices, s.slices] (stackedOf c0 t s ty) (by simp) hc
          (stackedOf_ma h0 ht hs hty) (I sh).ball (I sh).pinned (I sh).ball_append fun h hp ↦
          ⟨((I sh).ball_card h hp).1, ((I sh).ball_card h hp).2.trans (H.listL sh)⟩).frame
        (ExtT I SGood TGood sh x c0) fun h₀ l hr hj ↦
          extT_append sh x c0 (H.ncRing sh _ _ h₀ l hr) hj).mono
        (fun _ hp ↦ ⟨hp.1.1.1.1, hp.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hc hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun cl ↦
  ((HG sh cl).some.frame
    (fun h ↦ ExtAll I SGood TGood sh x h ∧ cl.Multiaffine sh.M ∧ BatchTie I sh cl h)
    fun h₀ l _ h ↦ ⟨extAll_append sh x h₀ l h.1, h.2.1, batchTie_append l h.1.1 h.2.2⟩).mono
    (fun _ hp ↦ ⟨hp.2.1.2, hp.2.1.1, hp.1.1, fun q hq hcl ↦
      (hp.2.2 q hq).1 ((hp.1.2 q hq hcl).2 c0 (by simp [stackedOf]))⟩)
    (fun _ _ hp hb ↦ ⟨hp.2.1, cl, hp.2.2.1, hp.2.2.2, hp.1 hb⟩) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hty hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hs hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ ht hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **After the commitment, with the opening's and the ring's facts**: `restSpec`'s two cases, the
`ExtAll` one by `extChainG`. -/
noncomputable def restSpecG (x : List UInt8) (c0 : StackClaim6) (h0 : c0.Multiaffine sh.M) :
    Spec (rest6 Φ sh (hdrView sh x) c0)
      (fun h ↦ (I sh).pinned h ∧ (commits h).length = 1 ∧ (I sh).Tied sh.M c0 h)
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h ∧ RG I GWc sh h) εI 0 0 := by
  classical
  refine (Spec.exPre (ι := Bool) (Pre := casePre (ExtT I SGood TGood sh x c0)
    (fun h ↦ JT I sh c0 h ∧ Doomed (I sh).cands (fun q ↦ GoodAll SGood TGood sh
      (hdrView sh x) q) h)) fun i ↦ ?_).mono (fun h hp ↦ ?_) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · cases i
    · exact (doomChain H sh (hdrView sh x) c0 h0).mono (fun _ h ↦ h) (fun b _ hb hb' ↦ by
        simp [hb] at hb') le_rfl le_rfl le_rfl
    · exact extChainG H HG sh x c0 h0
  · by_cases he : ExtAll I SGood TGood sh x h
    · exact ⟨true, ⟨he, hp.2.1⟩, hp.2.2⟩
    · exact ⟨false, hp, fun q hq hg ↦ he ⟨hp.1, q, hq, hg⟩⟩

open Classical in
/-- **The composed specification with the extractor's conjuncts**: `spec6` whose postcondition also
carries `RG` (the opening's claim multiaffine and tied to the candidates, the opening's facts `GWc`
for it), outside the doom precondition; escapes unchanged. -/
noncomputable def spec6G (vk : Digest) (x : List UInt8) :
    Spec (prog6 Φ sh vk x) (fun h ↦ h = [])
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h ∧ RG I GWc sh h) εI 0 0 :=
  ((H.commit sh).some.retInv (fun c0 ↦ c0.Multiaffine sh.M) (H.maCommit sh).ret).bind' fun c0 ↦
    if h0 : c0.Multiaffine sh.M then
      (restSpecG H HG sh x c0 h0).mono (fun _ hp ↦ hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ h0 hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end ChainG


/-! ## The certificate -/

theorem εI6_eq : ((εI6 : ℝ≥0) : ℝ≥0∞) = εI := by
  simp [εI6, εI, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv, ENNReal.inv_pow]

theorem zero_le_εI6 : (0 : ℝ≥0∞) ≤ (εI6 : ℝ≥0) := zero_le

/-- **`kcert6`'s hypothesis `SI`** for `schemeOf prog6`. -/
noncomputable def SI6 {Φ : Phases} {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
    (H : PhaseSpecs Φ I SGood TGood) (sh : Shape) (vk : Digest) (x : List UInt8) :
    Spec ((schemeOf (prog6 Φ) sh vk).P x) (fun h ↦ h = [])
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h) ((εI6 : ℝ≥0) : ℝ≥0∞) 0 0 :=
  (spec6 H sh vk x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) εI6_eq.ge le_rfl le_rfl

/-- **T5 for the composed scheme**: `kcert6` on `schemeOf prog6` at `P18`. -/
noncomputable def kcertAsm {Φ : Phases} {I : Shape → OpeningIface}
    {SGood TGood : Hdr → Stack → Prop} {R : Digest → Wit → Prop}
    (H : PhaseSpecs Φ I SGood TGood) (hF : PhasesFollow Φ P18) (vk : Digest)
    (X : Ext6 (schemeOf (prog6 Φ) P18 vk) R (ExtAll I SGood TGood P18)) :
    KCert (schemeOf (prog6 Φ) P18 vk) R :=
  kcert6 (prog6 Φ) P18 vk (SI6 H P18 vk) zero_le_εI6 (prog6_noGrind Φ hF vk) X

/-- **`Open6.sound` for `prog6`**: the phase statements, the schedule, the extractor's obligations
and `ExtEq6` give the certificate (F1's `sound6`). -/
theorem sound_asm {VS : Shape → SProg} {EX : Digest → RecursionFast.Proof → Log → Option Wit}
    {Φ : Phases}
    {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
    (H : PhaseSpecs Φ I SGood TGood) (hF : PhasesFollow Φ P18)
    (X : ∀ vk, Ext6 (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk))
      (ExtAll I SGood TGood P18))
    (hE : ∀ vk, ExtEq6 EX (kcertAsm H hF vk (X vk))) :
    ∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 EX K :=
  sound6 (Ext := fun _ ↦ ExtAll I SGood TGood P18) (fun vk ↦ SI6 H P18 vk) zero_le_εI6
    (fun vk ↦ prog6_noGrind Φ hF vk) X hE

/-- **`kcert6`'s hypothesis `SI` with the extractor's conjuncts**: `Ext x h = ExtAll … ∧ RG I GWc sh h`. -/
noncomputable def SI6G {Φ : Phases} {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
    (H : PhaseSpecs Φ I SGood TGood) {GWc : Shape → StackClaim6 → List Ev → Prop}
    (HG : Stmt.openGoodC GWc Φ.whir) (sh : Shape) (vk : Digest) (x : List UInt8) :
    Spec ((schemeOf (prog6 Φ) sh vk).P x) (fun h ↦ h = [])
      (fun b h ↦ b = true → ExtAll I SGood TGood sh x h ∧ RG I GWc sh h) ((εI6 : ℝ≥0) : ℝ≥0∞) 0 0 :=
  (spec6G H HG sh vk x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) εI6_eq.ge le_rfl le_rfl

/-- **T5 with the extractor's conjuncts**: `kcert6` on `schemeOf prog6` at `P18`, the extractor's `Ext`
being `ExtAll ∧ RG I GWc P18` (so `SFront6.goodL` may take `G x h := RG I GWc P18 h`, which names the
opening's claim, its facts `GWc P18 cl h` and its tie to the candidates). -/
noncomputable def kcertAsmG {Φ : Phases} {I : Shape → OpeningIface}
    {SGood TGood : Hdr → Stack → Prop} {R : Digest → Wit → Prop}
    {GWc : Shape → StackClaim6 → List Ev → Prop}
    (H : PhaseSpecs Φ I SGood TGood) (HG : Stmt.openGoodC GWc Φ.whir) (hF : PhasesFollow Φ P18)
    (vk : Digest)
    (X : Ext6 (schemeOf (prog6 Φ) P18 vk) R (fun x h ↦ ExtAll I SGood TGood P18 x h ∧ RG I GWc P18 h)) :
    KCert (schemeOf (prog6 Φ) P18 vk) R :=
  kcert6 (prog6 Φ) P18 vk (SI6G H HG P18 vk) zero_le_εI6 (prog6_noGrind Φ hF vk) X

/-- **`Open6.sound` for `prog6` with the extractor's conjuncts** (`sound_asm` with
`Ext = ExtAll ∧ RG`). -/
theorem sound_asmG {VS : Shape → SProg} {EX : Digest → RecursionFast.Proof → Log → Option Wit}
    {Φ : Phases}
    {I : Shape → OpeningIface} {SGood TGood : Hdr → Stack → Prop}
    {GWc : Shape → StackClaim6 → List Ev → Prop}
    (H : PhaseSpecs Φ I SGood TGood) (HG : Stmt.openGoodC GWc Φ.whir) (hF : PhasesFollow Φ P18)
    (X : ∀ vk, Ext6 (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk))
      (fun x h ↦ ExtAll I SGood TGood P18 x h ∧ RG I GWc P18 h))
    (hE : ∀ vk, ExtEq6 EX (kcertAsmG H HG hF vk (X vk))) :
    ∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 EX K :=
  sound6 (Ext := fun _ x h ↦ ExtAll I SGood TGood P18 x h ∧ RG I GWc P18 h)
    (fun vk ↦ SI6G H HG P18 vk) zero_le_εI6 (fun vk ↦ prog6_noGrind Φ hF vk) X hE

/-! ## The executable front refines `schemeOf prog6` -/

/-- **V1's decision for `prog6`**: replay `prog6` on the transcript read off `π`. -/
def F6 (Φ : Phases) (sh : Shape) (vk : Digest) (π : ByteArray) (acc : List V.NV) : Bool :=
  V.replay (prog6 Φ sh vk ((Lvm.Replay.bl π).take (V.hdrLen (toV sh))))
    (acc.map (V.NV.val π)).reverse

/-- **`V_S` for `prog6`**: V1's front with the decision `F6`. -/
def VSasm (Φ : Phases) (sh : Shape) : SProg := fun vk c π ↦ V.VS6 (toV sh) (F6 Φ sh vk) vk c π

/-- **T7 `refines6` for `prog6`** (V1's `VS6_refines`, `replay_refines`). -/
theorem refines6_asm (Φ : Phases) : Stmt.refines6 (VSasm Φ) (prog6 Φ) := by
  intro sh vk L c π _ h
  rw [VSasm, V.VS6_refines (toV sh) vk (fun x acc ↦ V.replay (prog6 Φ sh vk x) acc.reverse)
    (F6 Φ sh vk) (fun _ _ ↦ rfl)] at h
  exact V.replay_refines (toV sh) vk (prog6 Φ sh vk) L c π h

end Lvm6
