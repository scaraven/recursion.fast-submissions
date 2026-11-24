-- New for lvm6 (WP SPH): the sponge phase `SP.spongePhase6` meets ASM's obligations: its doom transfer
-- `Stmt.spongeSpec6` (K1's `spongeSpec6` for the caller and core, season 1's `ksLinkSpecE2` for the
-- link), `PhasesFollow.sponge` against `Shape.spongePart`, and `Stmt.noCommit`.
import Lvm6SpProg
import Lvm6AsmSpec
import Lvm6QKFollow
import Lvm6KSponge
import Lvm6KBridge
import Lvm6KNoCommit
import Lvm6KS6
import LvmE2VKS
import Lvm6MultiaffPhases
import Lvm6MultiaffSponge

/-!
# The sponge phase: specification, schedule, no commitment

* Placements on the stack (FORMAT6 §6.3, §6.5, CD): `spOf q` (the sponge block `SP`, slot 35),
  `yOf q ℓ` (`Y`'s lane `ℓ`, slot 36), `mOf q` (the stream words of slot 33, `17x + ℓ`), `xOf q`
  (`X`, slot 37, words `ℓ·2^10 + i`).
* **`SGood6 q`**: the sponge relation on the stack: K1's `RegionValid 13` and `OutRel 13 25` on
  `SP` and `Y`, and season 1's `SpongeLink 13 contRows6` with the message `ksMsg 7168 M X`.
* **`spongeSpecS6 : Stmt.spongeSpec6 spongePhase6 (fun _ ↦ SGood6)`**: K1's `spongeSpec6 13 25`
  (caller and core; the link relation carried), then `ksLinkSpecE2 13 10 contRows6` (the caller's
  claims carried), then `spS`: S's claims at 25 variables give K1's `SpongeClaims` and the link's
  `KsClaimsE2` (`claims_of_holds`; block claims by `col_splitF` and `sum_eqAtF_bitsF`). Season 1's
  doom shape becomes S's `DoomSpec` by K1's `doomSpec_of`.
* **`spongePhase6_follows`** (ASM's `PhasesFollow.sponge`), **`spongePhase6_noCommit`**.
* **`phases6_follows`**, **`phases6_specs`**: ASM's `PhasesFollow` and `PhaseSpecs` for `phases6` from
  the typed, ring and opening owners' facts only (commitment, tree and sponge are discharged here).
-/

set_option autoImplicit false

namespace Lvm6.SP

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open LeanVM.Protocol.KeccakGkr (RegionValid)
open Lvm.E2V Lvm6.K
open Lvm.ASM (εS)
open Finset

/-! ## Placements and the sponge relation -/

/-- The sponge block `SP` (slot 35; its word `x + 2^13·slot`). -/
def spOf (q : Stack) (x : ℕ) : K := q (x + 2 ^ 19 * 35)

/-- `Y`'s lane `l` at row `x` (slot 36, word `x + 2^13·l`). -/
def yOf (q : Stack) (l x : ℕ) : K := q (x + 2 ^ 13 * (36 * 64 + l))

/-- The message lanes below the split: stream word `17x + l` (slot 33). -/
def mOf (q : Stack) (x l : ℕ) : K := q (17 * x + l + 2 ^ 19 * 33)

/-- `X(i, l)`, the message lanes from the split (slot 37, word `l·2^10 + i`). -/
def xOf (q : Stack) (i l : ℕ) : K := q (i + 2 ^ 10 * (37 * 2 ^ 9 + l))

/-- The sponge link on the stack (season 1's `SpongeLink` over `contRows6`). -/
def LinkRel (q : Stack) : Prop :=
  Lvm.KG.SpongeLink 13 contRows6 (spOf q) (fun i l ↦ yOf q l i)
    (Lvm.KG.ksMsg (Lvm.KG.ksSplitN 13 10) (mOf q) (xOf q))

/-- **The sponge relation** of the stack (`ASM`'s `SGood`). -/
def SGood6 (q : Stack) : Prop :=
  RegionValid 13 (spOf q) ∧ Lvm.KG.OutRel 13 25 (spOf q) (yOf q) ∧ LinkRel q

/-! ## The continuation rows -/

theorem contRows6_bounds : ∀ i ∈ contRows6, 1 ≤ i ∧ i < 2 ^ 13 := by
  intro i hi
  simp only [contRows6, List.mem_append, List.mem_map, List.mem_range] at hi
  rcases hi with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;> norm_num <;> omega

theorem contRows6_nodup : contRows6.Nodup := by
  have h1 : ((List.range (4002 - 1)).map (· + 1)).Nodup :=
    List.nodup_range.map fun a b h ↦ by simpa using h
  have h2 : ((List.range 31).map (7567 + 1 + ·)).Nodup :=
    List.nodup_range.map fun a b h ↦ by simpa using h
  have h3 : ((List.range 31).map (8032 + 1 + ·)).Nodup :=
    List.nodup_range.map fun a b h ↦ by simpa using h
  unfold contRows6
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨h1, h2, ?_⟩, h3, ?_⟩
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_map, List.mem_range] at ha hb
    obtain ⟨y, hy, rfl⟩ := hb
    rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> omega

/-! ## Claims at 25 variables -/

theorem stepMleF_eq (w : ℕ) (pt : List E2) (f : ℕ → K) : stepMleF w pt f = stepMleK w pt f := rfl

theorem eqPt25 {p : List E2} (hp : p.length = 25) (x : ℕ) : eqPt p (boolPt 25 x) = eqAtF p x := by
  have e := K.eqPt_boolPt p x
  rwa [hp] at e

theorem stepMle25 {p : List E2} (hp : p.length = 25) (q : Stack) :
    ∑ x : Fin (2 ^ 25), eqPt p (boolPt 25 x) * algebraMap K E2 (q x) = stepMleK 25 p q := by
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqPt p (boolPt 25 x) * algebraMap K E2 (q x))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqPt25 hp]

/-- A point claim at 25 variables. -/
theorem pt_holds {p : List E2} (hp : p.length = 25) {v : E2} {q : Stack}
    (hH : StackClaim6.Holds 25 (fun pt ↦ eqPt p pt, v) q) : stepMleK 25 p q = v := by
  unfold StackClaim6.Holds at hH
  dsimp only at hH
  rw [← hH, stepMle25 hp]

/-- A combination of point claims at 25 variables. -/
theorem sum_holds {ι : Type} (s : Finset ι) (a : ι → E2) (p : ι → List E2)
    (hp : ∀ i ∈ s, (p i).length = 25) {v : E2} {q : Stack}
    (hH : StackClaim6.Holds 25 (fun pt ↦ ∑ i ∈ s, a i * eqPt (p i) pt, v) q) :
    ∑ i ∈ s, a i * stepMleK 25 (p i) q = v := by
  unfold StackClaim6.Holds at hH
  dsimp only at hH
  rw [← hH]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← stepMle25 (hp i hi), Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- **A block claim**: the high coordinates are the block index's bits. -/
theorem sum_block {h k o : ℕ} {a : List E2} (ha : a.length = h) (ho : o < 2 ^ k) (G : ℕ → E2) :
    ∑ n ∈ range (2 ^ (h + k)), eqAtF (a ++ bitsF o k) n * G n =
      ∑ x ∈ range (2 ^ h), eqAtF a x * G (x + 2 ^ h * o) := by
  have e := col_splitF (s := (bitsF o k : List E2)) ha G
  rw [bitsF_length] at e
  rw [e]
  exact sum_eqAtF_bitsF ho (fun o ↦ ∑ x ∈ range (2 ^ h), eqAtF a x * G (x + 2 ^ h * o))

theorem block25 {h k o : ℕ} {a : List E2} (ha : a.length = h) (hk : h + k = 25) (ho : o < 2 ^ k)
    (q : ℕ → K) : stepMleK 25 (a ++ bitsF o k) q = stepMleK h a (fun x ↦ q (x + 2 ^ h * o)) := by
  unfold stepMleK
  rw [← hk]
  exact sum_block ha ho (fun n ↦ kF (q n))

theorem stepMleK_bits {w : ℕ} (hw : w < 2 ^ 25) (q : ℕ → K) :
    stepMleK 25 (bitsF w 25 : List E2) q = kF (q w) := by
  unfold stepMleK
  exact sum_eqAtF_bitsF hw (fun n ↦ kF (q n))

theorem ksSplit_eq : Lvm.KG.ksSplitN 13 10 = 7168 := by
  unfold Lvm.KG.ksSplitN; norm_num

/-- **S's sponge claims give K1's and the link's** (lengths from the caller's and the link's
output). -/
theorem claims_of_holds {o : K.SpOut} (hs : K.SpongeShape 13 o) {lk : LinkOut}
    (hρ : lk.2.1.1.length = 13) {q : Stack} (hH : (spS o lk).Holds 25 q) :
    KsClaimsE2 13 10 (spOf q) (fun x l ↦ yOf q l x) (mOf q) (xOf q) (lk.1.drop 13) lk.2.1.1
        lk.2.2 ∧ K.SpongeClaims 13 25 (spOf q) (yOf q) o := by
  obtain ⟨hr, -, -, -, hϱ, -, hpt, hsl⟩ := hs
  have hC : ∀ c ∈ (spS o lk).claims, c.Holds 25 q := hH.2
  have hmem : ∀ c ∈ [cY lk, cIn lk, cM lk, cX lk], c ∈ (spS o lk).claims := fun c hc ↦
    List.mem_cons_of_mem _ (List.mem_append_right _ hc)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, fun i hi ↦ ?_⟩, fun l hl ↦ ?_⟩
  · have h := sum_holds (range 25) (fun l ↦ eqAtF (lk.1.drop 13) l)
      (fun l ↦ lk.2.1.1 ++ bitsF (36 * 64 + l) 12) (fun l _ ↦ by simp [hρ])
      (hC (cY lk) (hmem _ (by simp)))
    rw [← h]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [block25 hρ rfl (by norm_num; omega), stepMleF_eq]
    rfl
  · have h := sum_holds (range 25) (fun l ↦ eqAtF (lk.1.drop 13) l)
      (fun l ↦ lk.2.1.1 ++ bitsF (35 * 64 + l) 12) (fun l _ ↦ by simp [hρ])
      (hC (cIn lk) (hmem _ (by simp)))
    rw [← h]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [block25 hρ rfl (by norm_num; omega), stepMleF_eq]
    congr 2
    funext x
    unfold spOf
    congr 1
    ring
  · have h := sum_holds (range 17 ×ˢ range 7168)
      (fun i ↦ eqAtF (lk.1.drop 13) i.1 * eqAtF lk.2.1.1 i.2)
      (fun i ↦ bitsF (17 * i.2 + i.1 + 2 ^ 19 * 33) 25) (fun i _ ↦ by simp)
      (hC (cM lk) (hmem _ (by simp)))
    rw [← h, Finset.sum_product, ksSplit_eq]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hx' := Finset.mem_range.1 hx
    rw [stepMleK_bits (by norm_num; omega)]
    unfold mOf
    ring
  · have h := sum_holds (range 17) (fun l ↦ eqAtF (lk.1.drop 13) l)
      (fun l ↦ lk.2.1.1.take 10 ++ bitsF (37 * 2 ^ 9 + l) 15) (fun l _ ↦ by simp [hρ])
      (hC (cX lk) (hmem _ (by simp)))
    rw [← h]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [block25 (by simp [hρ]) rfl (by norm_num; omega), stepMleF_eq]
    rfl
  · simp [hr, hϱ]
  · have h := pt_holds (p := o.1 ++ o.2.2.1.ϱm ++ bitsF 35 6) (by simp [hr, hϱ])
      (hC _ List.mem_cons_self)
    rw [block25 (h := 19) (by simp [hr, hϱ]) rfl (by norm_num)] at h
    exact h
  · exact hpt
  · exact hsl
  · have h1 := hH.1 ⟨i, hi⟩
    simp only [spS] at h1
    rw [← h1, Fin.sum_univ_eq_sum_range
      (fun x ↦ eqPt (o.2.2.2.pt ++ bitsF 35 6) (boolPt 25 x) * bitE (q x) i)]
    have hlen : (o.2.2.2.pt ++ bitsF 35 6 : List E2).length = 25 := by simp [hpt]
    rw [Finset.sum_congr rfl fun x _ ↦ by rw [eqPt25 hlen]]
    refine (sum_block hpt (by norm_num : 35 < 2 ^ 6) (fun n ↦ bitE (q n) i)).trans ?_
    exact Finset.sum_congr rfl fun x _ ↦ by rw [K.bitE_eq]; rfl
  · have h := pt_holds (p := o.1 ++ bitsF (36 * 64 + l) 12) (by simp [hr])
      (hC _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))))
    rw [block25 hr rfl (by norm_num; omega)] at h
    exact h

/-! ## The doom transfer -/

variable {β : Type} [Finite β] {C : List Ev → Set β}

open Classical in
/-- **The sponge body in season 1's doom shape**: K1's caller and core with the link relation
carried, the link with the caller's claims carried, then the placement. -/
noncomputable def bodySpec (hst : Stable C) (hcard : ∀ hh, (C hh).ncard ≤ 1) (stk : β → Stack)
    (R : β → Prop) :
    Spec spongeBody (Doomed C (fun q ↦ SGood6 (stk q) ∧ R q))
      (fun out hist ↦ Doomed C (fun q ↦ out.Holds 25 (stk q) ∧ R q) hist) εS 0 0 :=
  ((K.spongeSpec6 13 25 (by norm_num) le_rfl C hst hcard (fun q ↦ spOf (stk q))
      (fun q ↦ yOf (stk q)) (fun q ↦ LinkRel (stk q) ∧ R q) 0 zero_le).some.mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨h1, h2, h3, hR⟩ ↦ ⟨⟨h1, h2, h3⟩, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun o ↦
  if hs : K.SpongeShape 13 o then
    ((ksLinkSpecE2 hst hcard 13 10 (by norm_num) contRows6 contRows6_nodup contRows6_bounds
        (fun q ↦ spOf (stk q)) (fun q x l ↦ yOf (stk q) l x) (fun q ↦ mOf (stk q))
        (fun q ↦ xOf (stk q)) (fun q ↦ K.SpongeClaims 13 25 (spOf (stk q)) (yOf (stk q)) o ∧ R q)
        (T := 0) zero_le).some.mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hl, hc, hR⟩ ↦ ⟨hc, hl, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun lk ↦
    (Spec.ret (Post := fun out hist ↦ Doomed C (fun q ↦ out.Holds 25 (stk q) ∧ R q) hist)
        (spS o lk)).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hH, hR⟩ ↦
        ⟨(claims_of_holds hs hd.1 hH).1, (claims_of_holds hs hd.1 hH).2, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **ASM's sponge obligation**: `Stmt.spongeSpec6 spongePhase6` with the relation `SGood6`. -/
theorem spongeSpecS6 : Stmt.spongeSpec6 spongePhase6 (fun _ q ↦ SGood6 q) := by
  intro sh x
  unfold spongePhase6
  split_ifs with hs
  · rw [hs.1]
    exact K.doomSpec_of fun {β} _ C hst hcard stk R ↦ ⟨bodySpec hst hcard stk R⟩
  · intro C R G _ _
    exact ⟨Spec.fail⟩

/-! ## The schedule and no commitment -/

theorem spongePart_P18 : P18.spongePart = QK.spItems 13 ++ QK.linkItems 13 := by
  simp only [Shape.spongePart, QK.spItems, QK.spCallerItems, QK.coreItems, QK.linkItems,
    List.append_assoc]
  rfl

theorem spongeBody_follows (L : List V.Lev) :
    Follows spongeBody (opsOf L (QK.spItems 13 ++ QK.linkItems 13)) := by
  rw [opsOf_append, ← List.append_nil (opsOf L (QK.linkItems 13))]
  exact Follows.bind' (QK.spCaller6_follows L 13 (by norm_num)) fun _ ↦
    Follows.bind' (QK.ksLink_follows L 13 10 contRows6) fun _ ↦ rfl

/-- **ASM's `PhasesFollow.sponge`**: the sponge phase follows `Shape.spongePart` at every shape. -/
theorem spongePhase6_follows (sh : Shape) (x : Hdr) :
    Follows (spongePhase6 sh x) (opsOf sh.levs sh.spongePart) := by
  unfold spongePhase6
  split_ifs with hs
  · rw [hs.2, spongePart_P18]
    exact spongeBody_follows sh.levs
  · trivial

/-- **The sponge phase commits nothing.** -/
theorem spongePhase6_noCommit (sh : Shape) (x : Hdr) : Stmt.noCommit (spongePhase6 sh x) := by
  have h : (spongePhase6 sh x).NoCommit := by
    unfold spongePhase6 spongeBody
    split_ifs
    · refine nc_bind' (nc_spCaller6 13) fun _ ↦ nc_bind' ?_ fun _ ↦ nc_ret _
      unfold ksLinkProgE2
      exact nc_bind' (nc_e2Samples _ _) fun _ ↦ nc_bind' (nc_sumcheckE2 _ _ _ _) fun _ ↦
        nc_bind' (nc_e2Reads _) fun _ ↦ nc_bind' (nc_require _) fun _ ↦ nc_ret _
    · trivial
  exact fun _ _ hl ↦ h.reach_commits hl

/-- `PhasesFollow.sponge` for ASM's `phases6`. -/
theorem phases6_sponge_follows
    (typed : Shape → Hdr → VerifierProgram (List StackClaim6))
    (ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6)
    (whir : Shape → StackClaim6 → VerifierProgram Bool) (sh : Shape) (x : Hdr) :
    Follows ((phases6 typed ring whir).sponge sh x) (opsOf sh.levs sh.spongePart) :=
  spongePhase6_follows sh x

/-- `PhaseSpecs.sponge` and `PhaseSpecs.ncSponge` for ASM's `phases6`. -/
theorem phases6_sponge_spec
    (typed : Shape → Hdr → VerifierProgram (List StackClaim6))
    (ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6)
    (whir : Shape → StackClaim6 → VerifierProgram Bool) :
    Stmt.spongeSpec6 (phases6 typed ring whir).sponge (fun _ q ↦ SGood6 q) ∧
      ∀ sh x, Stmt.noCommit ((phases6 typed ring whir).sponge sh x) :=
  ⟨spongeSpecS6, spongePhase6_noCommit⟩

/-- **`PhasesFollow` for `phases6`** from the typed, ring and opening phases' facts. -/
theorem phases6_follows {typed : Shape → Hdr → VerifierProgram (List StackClaim6)}
    {ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {whir : Shape → StackClaim6 → VerifierProgram Bool} {sh : Shape}
    (hty : ∀ x, Follows (typed sh x) (opsOf sh.levs (sh.subT.typed ++ sh.subT.bus)))
    (hr : ∀ sl st, Follows (ring sh sl st) (opsOf sh.levs sh.ringPart))
    (hw : ∀ cl, Follows (whir sh cl) (opsOf sh.levs sh.openPart)) :
    PhasesFollow (phases6 typed ring whir) sh :=
  ⟨commit6_follows sh, treeProgS6_follows sh, spongePhase6_follows sh, hty, hr, hw⟩

/-- **`PhaseSpecs` for `phases6`** (sponge relation `SGood6`) from the commitment's, typed, ring
and opening phases' statements; the multiaffinity of the commitment's, tree's and sponge's claims is
WP MA's (`commit6_ma`, `treeProgS6_ma`, `spongePhase6_ma`), the typed phases' a hypothesis (WP MA's
`typedPhase6_ma_at` for `Ty.typedPhase6`). -/
theorem phases6_specs {typed : Shape → Hdr → VerifierProgram (List StackClaim6)}
    {ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {whir : Shape → StackClaim6 → VerifierProgram Bool} {I : Shape → OpeningIface}
    {TGood : Hdr → Stack → Prop}
    (hc : Stmt.commitSpec6 I commit6) (hty : Stmt.typedSpecE typed TGood)
    (hr : Stmt.ringSpec6 ring) (ho : Stmt.openSpec6 I whir) (hL : ∀ sh, (I sh).L₀ ≤ sh.L₀)
    (ncT : ∀ sh x, Stmt.noCommit (typed sh x)) (ncR : ∀ sh sl st, Stmt.noCommit (ring sh sl st))
    (maT : Stmt.typedMA typed) :
    PhaseSpecs (phases6 typed ring whir) I (fun _ q ↦ SGood6 q) TGood :=
  ⟨hc, treeSpecS6, spongeSpecS6, hty, hr, ho, hL, treeProgS6_noCommit, spongePhase6_noCommit,
    ncT, ncR, commit6_ma, treeProgS6_ma, spongePhase6_ma, maT⟩

end Lvm6.SP
