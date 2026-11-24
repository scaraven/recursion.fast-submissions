-- lvm6 X8b: the v6 extractor's correctness assembled. `goodL` from `kcertAsmG` (the replayed history of an available
-- log is outside `kcert6`'s luck, so `SI6G`'s postcondition `ExtAll ∧ RG` holds on it); `descends` from the opening
-- read backwards (`Lvm6WhirBack`), `RG`'s batching tie and the pin, given the descent program's fact `DescProg6`;
-- `ext_eq6`, and the extractor-side fields of `Open6` (`sound` with `kcertAsmG`, `wBranch`, `computes`, `size`). New.
import Lvm6WhirBack
import Lvm6XFront
import Lvm6XDescProg
import Lvm6AsmSpec
import LvmCertSGood

/-!
# The extractor's correctness (X8b)

* `goodLv_goodL`: W1's `GoodLv` (from `GoodRs`, `goodRs_goodLv`) is X4's `GoodL` on the rounds' `(α, β)`.
* **`ext_of_avail`**: on an available log of `kcert6 … SI … X`, the replayed history satisfies `SI`'s `Ext`
  (`final_good`: not lucky, so inside `SI`'s doom, whose postcondition is `Ext`).
* `G6 SGood TGood x h := ExtAll I6 SGood TGood P18 x h ∧ RG I6 GW18c P18 h` (`kcertAsmG`'s `Ext` at W1's seam).
* **`pick6_eq_dec18`**: on a pinned history, a level-0 tuple of the list satisfying a claim tied to the candidates
  (`BatchTie`) decodes to `pick6`.
* **`DescProg6 Φ descX`** (open, X8a with X2's front): on an `S` proof of `pz6` bytes whose replay has the opening's
  facts for a multiaffine claim `cl`, the state before the output holds `dec18 U` for a level-0 tuple `U` of the list
  satisfying `cl` (`Back18`), with `Inv` and no output. **`Len6 Φ`** (open, F-X8b-1): an accepted `S` proof of the
  composed scheme has `pz6` bytes.
* **`descends6`**, **`sfront6`**, **`ext_eq6X`**, **`sound6X`**; **`open6X`**: `sound`, `wBranch`, `computes`, `size`
  of `Open6` for `EX6 (descX6 Lv fin)` / `extX6 (descX6 Lv fin)` from X7a's `LevelOk`/`LevelSz` of the descent.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm.T
open LeanVM.Protocol.Compile (Ev Spec)
open LeanVM.Parameters (E2)
open LeanVM.Protocol.Whir.AffineCombiner (DegLE agree)
open scoped NNReal ENNReal

/-! ## X4's `GoodL` from W1's `GoodLv` -/

theorem goodLv_goodL {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra BF64 F] {ℓ m d : ℕ}
    (dom : Fin (2 ^ ℓ) ↪ F) : ∀ (j : ℕ) (rs : List (Whir.Rnd F)) (Q : Whir.Wd F (2 ^ ℓ) (m + j)) (a : ℕ),
      Whir.GoodLv dom d j rs Q a → GoodL d dom j (rs.map fun r ↦ (r.α, r.β)) Q a
  | 0, _, _, _, _ => trivial
  | j + 1, rs, Q, a, h => by
    obtain ⟨h1, h2⟩ := h
    cases rs with
    | nil => exact ⟨goodLv_goodL dom j [] _ a h1, h2⟩
    | cons r rs => exact ⟨goodLv_goodL dom j rs _ a h1, h2⟩

/-! ## `goodL`: the postcondition on an available log -/

/-- **On an available log the replayed history satisfies `SI`'s `Ext`** (`kcert6`'s luck contains "outside
`SI`'s doom"; `final_good` puts the history outside luck). -/
theorem ext_of_avail {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool}
    {sh : Shape} {vk : Digest} {R : Digest → Wit → Prop} {Ext : List UInt8 → List Ev → Prop} {L' : ℝ≥0∞}
    {SI : ∀ x, Spec ((schemeOf prog sh vk).P x) (fun h ↦ h = []) (fun b h ↦ b = true → Ext x h)
      (εI6 : ℝ≥0∞) L' 0}
    {hL : L' ≤ εI6} {hng : ∀ x, (prog sh vk x).NoGrind} {X : Ext6 (schemeOf prog sh vk) R Ext}
    {c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hA : Avail (kcert6 prog sh vk SI hL hng X) c π L)
    (hE : (schemeOf prog sh vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h)) : Ext x h := by
  obtain ⟨-, -, hμ, hacc⟩ := hA
  obtain ⟨x', h', -, hr, ha, hB, -, -, hEx⟩ := Scheme.final_good _ L c π hμ hacc
  rw [hEx] at hE
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hE)
  have hD : (SI x').D [] h' := by
    by_contra hD
    exact hB (Or.inl hD)
  exact (SI x').post (LeanVM.Protocol.Compile.VerifierProgram.reach_nil_iff.2 hr) ha hD rfl

/-- **The extractor's `G`**: `kcertAsmG`'s `Ext` at W1's seam `I6` and facts `GW18c`. -/
def G6 (SGood TGood : Hdr → Stack → Prop) (x : List UInt8) (h : List Ev) : Prop :=
  ExtAll Whir.I6 SGood TGood P18 x h ∧ RG Whir.I6 Whir.GW18c P18 h

section Seam

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GW18c Φ.whir) (hF : PhasesFollow Φ P18)

/-- **`SFront6.goodL`** for `kcertAsmG`. -/
theorem goodL6 (vk : Digest) {R : Digest → Wit → Prop}
    (X : Ext6 (schemeOf (prog6 Φ) P18 vk) R (G6 SGood TGood)) (c : Digest) (π : Proof) (L : Log)
    (hA : Avail (kcertAsmG H HG hF vk X) c π L) (x : List UInt8) (h : List Ev)
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h)) : G6 SGood TGood x h :=
  ext_of_avail hA hE

end Seam

/-! ## `descends`: the pinned candidate is the decoded tuple's stack -/

theorem I6_P18 : Whir.I6 P18 = Whir.I18 := if_pos Whir.openKey_P18

/-- **The decoded tuple's stack is `pick6`**: on a pinned history, a level-0 tuple of the list satisfying a claim
tied to the candidates decodes to the pinned candidate. -/
theorem pick6_eq_dec18 {h : List Ev} {cl : StackClaim6} {U : Whir.Tup E2 (0 + 6)}
    (hp : (Whir.I6 P18).pinned h) (ht : BatchTie Whir.I6 P18 cl h) (hU : Whir.Back18 cl h U) :
    pick6 (Whir.I6 P18) h = Whir.dec18 U := by
  obtain ⟨hb, hcl⟩ := Whir.back18_holds cl h U hU.1 hU.2.1 hU.2.2
  have hc : Whir.dec18 U ∈ (Whir.I6 P18).cands h := ht _ (by rw [I6_P18]; exact hb) hcl
  exact (Whir.I6 P18).pinned_sub h hp (pick6_mem ⟨_, hc⟩) hc

/-- **The descent program's fact** (X8a, with X2's front; open): on an `S` proof of `pz6` bytes whose replayed
history carries the opening's facts for a multiaffine claim `cl`, the state before the output holds the stack of a
level-0 tuple of the list satisfying `cl` (from `colB6`), with `Inv` and no output. -/
def DescProg6 (Φ : Phases) (descX : XIR) : Prop :=
  ∀ vk c π L x h, (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h) → π.size = pz6 →
    ∀ cl : StackClaim6, cl.Multiaffine 25 → Whir.GW18c P18 cl h →
      ∃ U, Whir.Back18 cl h U ∧ Inv (preOut6 descX (extractorInput c π L)).M ∧
        (preOut6 descX (extractorInput c π L)).o = #[] ∧
        HeapHolds (preOut6 descX (extractorInput c π L)).M (Whir.dec18 U)

/-- **The length fact** (open, F-X8b-1): an accepted `S` proof of the composed scheme has `pz6` bytes. -/
def Len6 (Φ : Phases) : Prop :=
  ∀ vk c π L, isS π = true → ((schemeOf (prog6 Φ) P18 vk).V c π).runLog L = some true → π.size = pz6

/-- **`SFront6.descends`** from the descent program's fact. -/
theorem descends6 {Φ : Phases} {descX : XIR} (hD : DescProg6 Φ descX) {SGood TGood : Hdr → Stack → Prop}
    (vk : Digest) (c : Digest) (π : Proof) (L : Log) (x : List UInt8) (h : List Ev)
    (hE : (schemeOf (prog6 Φ) P18 vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h)) (hl : π.size = pz6)
    (hG : G6 SGood TGood x h) :
    Inv (preOut6 descX (extractorInput c π L)).M ∧ (preOut6 descX (extractorInput c π L)).o = #[] ∧
      HeapHolds (preOut6 descX (extractorInput c π L)).M (pick6 (Whir.I6 P18) h) := by
  obtain ⟨hX, hR⟩ := hG
  obtain ⟨cl, hma, hgw, ht⟩ := RG.mem_cands hR
  obtain ⟨U, hU, hI, hO, hH⟩ := hD vk c π L x h hE hl cl hma hgw
  rw [pick6_eq_dec18 hX.1 ht hU]
  exact ⟨hI, hO, hH⟩

/-! ## `ext_eq6` and `Open6`'s extractor fields -/

section Assembly

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GW18c Φ.whir) (hF : PhasesFollow Φ P18) {VS : Shape → SProg}
  (X : ∀ vk, Ext6 (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)) (G6 SGood TGood))

/-- **`SFront6`** for `kcertAsmG`: `len`, `goodL`, `descends` (`hdrTape`, `childFits`: X6a). -/
theorem sfront6 {descX : XIR} (hlen : Len6 Φ) (hD : DescProg6 Φ descX) (vk : Digest) :
    SFront6 (kcertAsmG H HG hF vk (X vk)) (Whir.I6 P18) descX (G6 SGood TGood) :=
  SFront6.ofOpen (fun c π L hA ↦ hlen vk c π L hA.1 hA.2.2.2) (goodL6 H HG hF vk (X vk))
    (descends6 hD vk)

/-- **T8 `ext_eq6`** for `kcertAsmG` with the extraction map `ExtSpec6 (I6 P18)`. -/
theorem ext_eq6X {descX : XIR} (hX : ∀ vk, (X vk).ext = ExtSpec6 (Whir.I6 P18)) (hlen : Len6 Φ)
    (hD : DescProg6 Φ descX) (vk : Digest) : ExtEq6 (EX6 descX) (kcertAsmG H HG hF vk (X vk)) :=
  ext_eq6 _ (Whir.I6 P18) (hX vk) (sfront6 H HG hF X hlen hD vk)

include H HG hF in
/-- **`Open6.sound`** for `prog6 Φ` and the extractor `EX6 descX` (`sound_asmG`). -/
theorem sound6X {descX : XIR} (hX : ∀ vk, (X vk).ext = ExtSpec6 (Whir.I6 P18)) (hlen : Len6 Φ)
    (hD : DescProg6 Φ descX) :
    ∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 descX) K :=
  sound_asmG H HG hF X (ext_eq6X H HG hF X hX hlen hD)

include H HG hF in
/-- **The extractor's fields of `Open6`** at the descent `descX6 Lv fin`: `sound` (with `kcertAsmG`), `wBranch`,
`computes` (fuel `2^47 + 8192·t`), `size` (`≤ progCap`), from the descent's structural and size budgets (X7a) and
the open facts `Len6`, `DescProg6`. -/
theorem open6X {Lv : ℕ → LevelX} {fin : XIR} (hX : ∀ vk, (X vk).ext = ExtSpec6 (Whir.I6 P18))
    (hlen : Len6 Φ) (hD : DescProg6 Φ (descX6 Lv fin)) (hL : ∀ i < 5, LevelOk i (Lv i))
    (hf : PartOk fin finCap) (hS : ∀ i < 5, LevelSz i (Lv i)) (hfs : sizeIR fin ≤ finSz) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P18 vk) (Rel (accV (VS P18) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (descX6 Lv fin)) K) ∧
    (∀ c π L, isS π = false → EX6 (descX6 Lv fin) c π L = RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (descX6 Lv fin)) (EX6 (descX6 Lv fin)) fuel6 ∧
    (extX6 (descX6 Lv fin)).body.size ≤ progCap :=
  ⟨sound6X H HG hF X hX hlen hD, wBranch6 _, computes6_descX6 hL hf, size_extX6 (sizeIR_descX6_le hS hfs)⟩

end Assembly

/-- W1's opening provides `HG` for phases whose opening is the deployed one. -/
theorem openGoodC_W1 : Stmt.openGoodC Whir.GW18c (whirAt Whir.whirP18) := Whir.openGood_W1C

end Lvm6.X
