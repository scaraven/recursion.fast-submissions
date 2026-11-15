-- New for lvm2 roll 11 (M′, R11-LEAD freeze 2026-11-13): the `S` branch's certificate with one commitment
-- (`C_rec` merged into `C_main`). Definitions are final; the `sorry`s are frozen statements (owner: R11-C,
-- except `extJM`'s decoders, R11-X). A proof never changes its statement; a needed change is reported old → new.
import LvmSubmissionS
import LvmCertSNo
import LvmMPDec
import LvmMPCertOpen
import LvmMPCertSplit
import LvmCertSExtJ

-- ===== merged from `LvmMPCertExt` (GOLF module merge: `LvmMPCertExt.lean` is now a stub importing `LvmMPCert`) =====
section
-- New for lvm2 roll 11 (M′, R11-C): the decoders succeed at M′ (`LvmMPCert`'s `extJM`), from a good residual and
-- no luck. Adapted from `LvmCertSExtJ.decode_SJ` (two levels of `C_rec`) to `C_main`'s three levels; the decoders'
-- correctness is `LvmMPDec`'s (`decodeMP2_of_mem`, `decodeMP1_of_mem`, `decodeMP0_of_mem`, R11-X), used as stated.

/-!
# M′'s decoders succeed

**`decode_SMH`**: after a completed run `h₁` of M′'s program up to `C_main`'s residual whose residual is good
(`GoodResM`, for a good set `G`), with well-shaped commitments and no luck (`LuckBM`) on `h₁ ++ t`, the chain
`decodeMP2` (level-2 word, `α₂`, residual) → `decodeMP1` (level-1 word, `α₁`) → `decodeMP0` (root word, `α₀`)
returns the stream window of a good root candidate `q`. The fold challenges are read as `LvmMPCert`'s `extSM`
reads them: `α₀ = folds[0,6)`, `α₁ = folds[6,10)`, `α₂ = folds[10,14)` of the final fold state.

The proof: `mainPrefix_split` gives the run's words `W₀, W₁, W₂` and fold states; `goodRes_main23JqH` gives `q`,
the level-1 member `V₁` and the level-2 member `V₂` on `q`'s path and the residual on it; the path lemmas
(`sum_eqW_path`, `pathAt_joinMsg_iff`, `pathAt_zero_iff_foldMsg`) give the decoders' fold relations; off
`LuckBM` (`readersM_of_split`, `roundsLuck_of_foldAllLuck`) the three are not lucky.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud

theorem getD_append_lt (l₁ l₂ : List E) {i : ℕ} (hi : i < l₁.length) : (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem getD_append_add (l₁ l₂ : List E) {n : ℕ} (hn : l₁.length = n) (i : ℕ) :
    (l₁ ++ l₂).getD (n + i) 0 = l₂.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
  congr 1
  omega

section Decode

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {x : List UInt8}

/-- **M′'s decoders succeed** on a good residual off luck: the chain returns a good candidate's window. -/
theorem decode_SMH {G : LeanVM.Protocol.Column CMain.nu20 → Prop} (hnc : (mid x).NoCommit) {h₁ t : List Ev}
    {cl : List LeanVM.Protocol.Verifier.StackClaim} {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
      stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ VerifierProgram.ret (cl, a)).after h₁ = some (.ret (cl, a)))
    (hG : GoodResM G a h₁) (hws : ∀ ht w W, Ev.commit ht w W ∈ h₁ ++ t → WellShaped w W)
    (hB : ¬ LuckBM mid x (h₁ ++ t)) :
    ∃ q, G q ∧
      ((Lvm.X.decodeMP2 (Lvm.X.wdOf (wordOf (commits (h₁ ++ t)) 2))
          (Lvm.X.alphaN1 fun i ↦ a.2.1.1.folds.getD (10 + i) 0) (Lvm.X.fNk 9 (resMsg a.2.2))).bind fun m₂ ↦
        (Lvm.X.decodeMP1 (Lvm.X.wdOf (wordOf (commits (h₁ ++ t)) 1))
            (Lvm.X.alphaN1 fun i ↦ a.2.1.1.folds.getD (6 + i) 0) m₂).bind fun m₁ ↦
          Lvm.X.decodeMP0 (Lvm.X.wdOf (wordOf (commits (h₁ ++ t)) 0))
            (Lvm.X.alphaN fun i ↦ a.2.1.1.folds.getD i 0) m₁) = some (Lvm.X.winOf q) := by
  obtain ⟨W₀, lm, ρ, lq, lf0, r0, ht1, W₁, lm0, lf1, r1, ht2, W₂, lm1, lf2, r2, lres, res, hh₁, rfl, hmid,
    hlq, hlqs, hf0, hf0s, hl0, hr0, hm0, hm0s, hf1, hf1s, hl1, hr1, hm1, hm1s, hf2, hf2s, hl2, hr2, hres,
    -⟩ := mainPrefix_split hpre
  have hlm := NoCommit.after_commits hnc hmid
  -- the commitments
  have hcs : commits h₁ = [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)] := by
    rw [hh₁]
    simp only [commits, LeanVM.Protocol.Whir.Sound.commits_append, hlm, hlq, hf0, hm0, hf1, hm1, hf2, hres,
      List.nil_append]
  have hw : ∀ j, j < 3 → wordOf (commits (h₁ ++ t)) j =
      wordOf [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)] j := fun j hj ↦ by
    rw [LeanVM.Protocol.Whir.Sound.commits_append, hcs]
    exact wordOf_append_of_lt _ _ hj
  have hw0 : wordOf (commits (h₁ ++ t)) 0 = W₀ := hw 0 (by omega)
  have hw1 : wordOf (commits (h₁ ++ t)) 1 = W₁ := hw 1 (by omega)
  have hw2 : wordOf (commits (h₁ ++ t)) 2 = W₂ := hw 2 (by omega)
  -- the good residual, unfolded
  unfold GoodResM at hG
  rw [hcs, show viewC 0 1 [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)] =
    [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)] from rfl] at hG
  dsimp only at hG ⊢
  have hF : r2.1.folds = r0.2 ++ r1.2 ++ r2.2 := by rw [hr2, hr1, hr0]
  have ha0 : (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r2.1.folds.getD i 0) =
      fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r0.2.getD i 0 :=
    funext fun i ↦ by rw [hF, List.append_assoc, getD_append_lt _ _ (by rw [hl0]; exact i.2)]
  have ha1 : (fun i : Fin 4 ↦ r2.1.folds.getD (6 + i) 0) = fun i : Fin 4 ↦ r1.2.getD i 0 :=
    funext fun i ↦ by
      rw [hF, List.append_assoc, getD_append_add _ _ hl0, getD_append_lt _ _ (by rw [hl1]; exact i.2)]
  have ha2 : (fun i : Fin 4 ↦ r2.1.folds.getD (10 + i) 0) = fun i : Fin 4 ↦ r2.2.getD i 0 :=
    funext fun i ↦ by rw [hF, getD_append_add _ _ (by rw [List.length_append, hl0, hl1])]
  have hfs : r2.1.folds = List.ofFn (fun i : Fin 6 ↦ r2.1.folds.getD i 0) ++
      List.ofFn (fun i : Fin 4 ↦ r2.1.folds.getD (6 + i) 0) ++
      List.ofFn (fun i : Fin 4 ↦ r2.1.folds.getD (10 + i) 0) := by
    rw [ha1, ha2, show (fun i : Fin 6 ↦ r2.1.folds.getD i 0) = fun i : Fin 6 ↦ r0.2.getD i 0 from ha0,
      ofFn_getD_eq _ hl0, ofFn_getD_eq _ hl1, ofFn_getD_eq _ hl2, hF]
  obtain ⟨q, hq0, hgood, hc1, hc2, hresq⟩ := goodRes_main23JqH _ _ _ hfs hG
  have hrows1 : rowsOf 4 (laneO 1 [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)]
      (codesMain23Jq 1).n) = rows1 4 (codesMain23Jq 1).n W₁ := rfl
  have hrows2 : rowsOf 4 (laneO 2 [(19, 64, W₀), (ht1, 3 * 2 ^ 4, W₁), (ht2, 3 * 2 ^ 4, W₂)]
      (codesMain23Jq 2).n) = rows1 4 (codesMain23Jq 2).n W₂ := rfl
  rw [hrows1] at hc1
  rw [hrows2] at hc2
  obtain ⟨V₁, hV₁, hp1⟩ := exists_iList_parts hc1
  obtain ⟨V₂, hV₂, hp2⟩ := exists_iList_parts hc2
  -- the words' shapes
  have hW₀ : WellShaped 64 W₀ := hws 19 64 W₀ (by rw [hh₁]; simp)
  have hW₁ : WellShaped (3 * 2 ^ 4) W₁ := hws ht1 _ W₁ (by rw [hh₁]; simp)
  have hW₂ : WellShaped (3 * 2 ^ 4) W₂ := hws ht2 _ W₂ (by rw [hh₁]; simp)
  -- the luck's readers
  obtain ⟨hd0, hch0, hd1, hch1, hd2, hch2⟩ := readersM_of_split (mid := mid) (x := x) (T := lres ++ t)
    (h := h₁ ++ t) (W₀ := W₀) (W₁ := W₁) (W₂ := W₂) (ρ := ρ) (ht1 := ht1) (ht2 := ht2) (w1 := 3 * 2 ^ 4)
    (w2 := 3 * 2 ^ 4)
    hmid hlq hlqs hf0 hf0s hl0 hm0 hm0s hf1 hf1s hl1 hm1s hf2s hl2 (by rw [hh₁]; simp)
  have nl0 : ¬ FoldAllLuck (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r2.1.folds.getD i 0)
      (laneRows CMain.nu20 2 W₀) (encRows CMain.nu20 2 q) := by
    intro hFL
    refine hB (.inl ?_)
    unfold LuckR
    rw [hd0, hch0]
    exact ⟨_, ⟨q, hq0, rfl⟩, roundsLuck_of_foldAllLuck _ _ _ _ hl0 (by rw [← ha0]; exact hFL)⟩
  have nl1 : ¬ FoldAllLuck (fun i : Fin 4 ↦ r2.1.folds.getD (6 + i) 0) (rows1 4 (codesMain23Jq 1).n W₁) V₁ := by
    intro hFL
    refine hB (.inr (.inl ?_))
    unfold LuckR
    rw [hd1, hch1]
    refine ⟨V₁, ?_, roundsLuck_of_foldAllLuck _ _ _ _ hl1 (by rw [← ha1]; exact hFL)⟩
    unfold ΛjM
    rw [Finset.mem_coe, mem_iList]
    exact hV₁
  have nl2 : ¬ FoldAllLuck (fun i : Fin 4 ↦ r2.1.folds.getD (10 + i) 0) (rows1 4 (codesMain23Jq 2).n W₂) V₂ := by
    intro hFL
    refine hB (.inr (.inr ?_))
    unfold LuckR
    rw [hd2, hch2]
    refine ⟨V₂, ?_, roundsLuck_of_foldAllLuck _ _ _ _ hl2 (by rw [← ha2]; exact hFL)⟩
    unfold ΛjM
    rw [Finset.mem_coe, mem_iList]
    exact hV₂
  -- the decoders' fold relations
  have hf₂ : resMsg res = ∑ u, eqW (fun i : Fin 4 ↦ r2.1.folds.getD (10 + i) 0) u • decode (codesMain23Jq 2) V₂ u :=
    funext fun y ↦ by rw [hresq y, sum_eqW_path q _ _ _ hp2 y]
  have hf₁ : joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V₂) =
      ∑ u, eqW (fun i : Fin 4 ↦ r2.1.folds.getD (6 + i) 0) u • decode (codesMain23Jq 1) V₁ u :=
    funext fun y ↦ by
      have := (pathAt_joinMsg_iff (by rfl : 13 = 4 + (codesMain23Jq 2).κ) q _ _).mpr hp2 Fin.elim0 y
      simp only [bitsL_zero, List.append_nil] at this
      rw [sum_eqW_path q _ _ _ hp1 y]
      exact this
  have hjoin : joinMsg (by rfl : 17 = 4 + (codesMain23Jq 1).κ) (decode (codesMain23Jq 1) V₁) =
      foldMsg (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r2.1.folds.getD i 0) q :=
    (pathAt_zero_iff_foldMsg q _ _).mp ((pathAt_joinMsg_iff _ q _ _).mpr hp1)
  -- the decoders
  have hdec2 : Lvm.X.decodeMP2 (Lvm.X.wdOf W₂) (Lvm.X.alphaN1 fun i ↦ r2.1.folds.getD (10 + i) 0)
      (Lvm.X.fNk 9 (resMsg res)) =
      some (Lvm.X.fNk 13 (joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V₂))) :=
    Lvm.X.decodeMP2_of_mem W₂ (fun v _ ↦ hW₂ v) _ (resMsg res) V₂ hV₂.1
      (by norm_num [codesMain23Jq, codeJ9R4]) hV₂.2 hf₂ nl2
  have hdec1 : Lvm.X.decodeMP1 (Lvm.X.wdOf W₁) (Lvm.X.alphaN1 fun i ↦ r2.1.folds.getD (6 + i) 0)
      (Lvm.X.fNk 13 (joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V₂))) =
      some (Lvm.X.fNk 17 (foldMsg (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r2.1.folds.getD i 0) q)) := by
    rw [← hjoin]
    exact Lvm.X.decodeMP1_of_mem W₁ (fun v _ ↦ hW₁ v) _ _ V₁ hV₁.1
      (by norm_num [codesMain23Jq, codeJ13R3]) hV₁.2 hf₁ nl1
  have hdec0 : Lvm.X.decodeMP0 (Lvm.X.wdOf W₀) (Lvm.X.alphaN fun i ↦ r2.1.folds.getD i 0)
      (Lvm.X.fNk 17 (foldMsg (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r2.1.folds.getD i 0) q)) =
      some (Lvm.X.winOf q) :=
    Lvm.X.decodeMP0_of_mem W₀ _ q (fun v _ ↦ hW₀ v) hq0 (by norm_num [codesMain23Jq, codeJ17R2]) nl0
  refine ⟨q, hgood, ?_⟩
  rw [hw0, hw1, hw2, hdec2, Option.bind_some, hdec1, Option.bind_some, hdec0]

end Decode

end Lvm.ASM
end
-- ===== end of `LvmMPCertExt` =====

/-!
# M′'s certificate: one root, INV on `C_main`

M′ commits one word, `C_main` at ν = 23 (`cfgMain23Jq 1`: `(6,2,115)(4,3,77)(4,4,58)`, OOD, `g = 14`). The
stream, `σ'` and every recursion table sit in `C_main`; the middle phases return claims on `C_main` only.

INV (J2C-DES, `kcertOfInv`) with one list: the middle phases leave every **non-good** candidate of `C_main`
failing a claim (`OpenPostM`, list `≤ 124`, so `L₀ = 124`); `C_main`'s opening runs JB-L's relativised prefix
(`stackedPrefixSpecR` at `codesMain23Jq`, good set `Good x`) to the residual, where `GoodRes ∨ ResC`;
`ResC` is rejected by the suffix (`finSuffixSpecR`), `GoodRes` is recorded as `ExtIM`. No split at the
openings (`openPostR_split` goes) and no `GoodRec`.

The extractor decodes `C_main` from the residual: level 2, level 1, then level 0's stream window
(`LvmMPDec`), with luck over the three levels' lists (14 fold rounds).

* defs: `GoodRelM`, **`PSWithM`**, `RootShapeM`, `OpenPostM`, **`MidSpecM`**, `MidShapeM`, `mainPrefixProg`,
  `GoodResAtM`, **`ExtIM`**, `ExtJM`, **`NodeSoundM`**, `mainDataM`, **`extSM`**, `OpenSM`;
* frozen: `ng_PSWithM`, **`psInvM`**, `goodRes_main23Jq`, **`extJM`**, `extJM_ext`;
* assembled here: **`kcertSM`**, **`εFS_kcertSM`** (`≤ 2^-128`), **`sSound_of_openSM`**.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal

/-! ## Definitions -/

/-- The M3 witness relation on one `C_main` candidate (physical stack; the shape's view is the instance's). -/
abbrev GoodRelM : Type := List UInt8 → LeanVM.Protocol.Column CMain.nu20 → Prop

/-- **The IOP verifier `P_S` at M′**: one root (`cfgMain24G`'s root = `cfgMain23Jq`'s), the middle phases
(claims on `C_main` only), `C_main`'s Johnson opening with `n₀ = 1` commitment before it. -/
def PSWithM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    VerifierProgram Bool := do
  commitRootUd cfgMain24G
  let cl ← mid x
  verifyStackedJ (cfgMain23Jq 1) cl
  return true

/-- The root's shape, and nothing else committed. -/
def RootShapeM (h : List Ev) : Prop :=
  ∃ W, commits h = [(19, 64, W)] ∧ WellShaped 64 W

/-- **The middle phases' postcondition at M′**: every non-good candidate of `C_main` fails a claim; the root's
shape; multiaffine claims, at most `2^40` (`eBatch_main23Jq`). -/
def OpenPostM (Good : GoodRelM) (x : List UInt8) (cl : List LeanVM.Protocol.Verifier.StackClaim) (h : List Ev) : Prop :=
  (∀ q ∈ Candidates CMain.nu20 2 thrMain (wordOf (commits h) 0), ¬ Good x q →
      ∃ c ∈ cl, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c q) ∧
  RootShapeM h ∧ (∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) ∧ cl.length ≤ 2 ^ 40

/-- **Obligation `MidSpecM`**: the middle phases, from the root's shape, end in `OpenPostM`, every group's
escape at most `εm`, lead `Lm`, for every follower's allowance `T ≤ εm`. -/
def MidSpecM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (εm Lm : ℝ≥0∞) :
    Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm → Nonempty (Spec (mid x) RootShapeM (OpenPostM Good x) εm Lm T)

/-- The middle phases commit nothing and grind nothing. -/
structure MidShapeM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) : Prop where
  noCommit : ∀ x, (mid x).NoCommit
  noGrind : ∀ x, (mid x).NoGrind

/-- **The run up to `C_main`'s residual**: the root, the middle phases, `C_main`'s opening up to the residual. -/
def mainPrefixProg (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim × E × ((WhirStateT × List E) × List E)) :=
  commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
    stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ .ret (cl, a)

/-- **The residual is good** (`PostR`'s left disjunct at `cfgMain23Jq 1`, final level `2`, good root set
`Good x`). -/
def GoodResAtM (Good : GoodRelM) (x : List UInt8) (a : E × ((WhirStateT × List E) × List E))
    (h₁ : List Ev) : Prop :=
  let cs := viewC 0 1 (commits h₁)
  GoodRes (codesMain23Jq 2) 2
    (gdFinal codesMain23Jq cs a.2.1.1.folds 0 0 (cfgMain23Jq 1).levels (gdRoot (codesMain23Jq 0) (Good x) cs))
    a.2.1 a.2.2 cs

/-- **What an accepting run in the invariant has**: a prefix is a completed `mainPrefixProg` run with a good
residual. -/
def ExtIM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (x : List UInt8)
    (h : List Ev) : Prop :=
  ∃ h₁ cl a, h₁ <+: h ∧ (mainPrefixProg mid x).after h₁ = some (.ret (cl, a)) ∧ GoodResAtM Good x a h₁

theorem ExtIM.append {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {x : List UInt8} {h : List Ev} (hE : ExtIM mid Good x h) (l : List Ev) : ExtIM mid Good x (h ++ l) := by
  obtain ⟨h₁, cl, a, hp, ha, hg⟩ := hE
  exact ⟨h₁, cl, a, hp.trans (List.prefix_append h l), ha, hg⟩

/-- **The extraction's interface at M′** (as `ExtJ`, on `PSWithM` and `ExtIM`). -/
structure ExtJM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM) (VS : SProg)
    (vk : Digest) : Type where
  BL : List UInt8 → List Ev → Prop
  BL_nil : ∀ x, ¬ BL x []
  BL_read : ∀ {x h k} (y : E), (PSWithM mid x).Reachable h → (PSWithM mid x).after h = some (.read k) →
    ¬ BL x h → ¬ BL x (h ++ [Ev.read y])
  BL_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (PSWithM mid x).Reachable h →
    (PSWithM mid x).after h = some (.commit ht w k) → WellShaped w word → ¬ BL x h →
    ¬ BL x (h ++ [Ev.commit ht w word])
  BL_group : ∀ {x h p}, (PSWithM mid x).Reachable h → Boundary h → (PSWithM mid x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ BL x h →
    esc (fun h' => ¬ BL x h') h p ≤ (((2 : ℝ≥0)⁻¹ ^ 132 : ℝ≥0) : ℝ≥0∞)
  ext : Digest → List UInt8 → List Ev → Wit
  extract : ∀ {c x h}, okS vk c x = true → (PSWithM mid x).Reachable h →
    (PSWithM mid x).after h = some (.ret true) → ExtIM mid Good x h → ¬ BL x h →
    (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → Rel (accV VS vk) c (ext c x h)

/-- **Obligation `NodeSoundM`**: a statement the header check accepts and a good `C_main` candidate give the
relation for the witness whose left child is read from the candidate's stream window (`winOf`; `child` reads the
stream at the statement's shape). -/
def NodeSoundM (VS : SProg) (vk : Digest) (Good : GoodRelM)
    (child : List UInt8 → List BF64 → Signed) : Prop :=
  ∀ c x q, okS vk c x = true → Good x q → Rel (accV VS vk) c (witOf x (child x (Lvm.X.winOf q)))

/-- **`C_main`'s values**, read off a history as `mainPrefixProg`'s return: all fold challenges (`6 + 4 + 4`)
and the residual. -/
def mainDataM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) (h : List Ev) :
    Option (List E × List E) :=
  match (mainPrefixProg mid x).retSplit h with
  | none => none
  | some ((_, _, r, res), _, _) => some (r.1.folds, res)

/-- **M′'s extraction map**: the three decoders on `C_main`'s words (`commits h` `0, 1, 2`), the fold challenges
`α₀ = folds[0,6)`, `α₁ = folds[6,10)`, `α₂ = folds[10,14)` and the residual; the witness with the child read
from the decoded window. No choice. -/
noncomputable def extSM (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim))
    (child : List UInt8 → List BF64 → Signed) (_c : RecursionFast.Digest) (x : List UInt8) (h : List Ev) :
    Wit :=
  witOf x (child x (((mainDataM mid x h).bind fun d ↦
    (Lvm.X.decodeMP2 (Lvm.X.wdOf (wordOf (commits h) 2)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (10 + i) 0)
        (Lvm.X.fNk 9 (resMsg d.2))).bind fun m₂ ↦
      (Lvm.X.decodeMP1 (Lvm.X.wdOf (wordOf (commits h) 1)) (Lvm.X.alphaN1 fun i ↦ d.1.getD (6 + i) 0)
          m₂).bind fun m₁ ↦
        Lvm.X.decodeMP0 (Lvm.X.wdOf (wordOf (commits h) 0)) (Lvm.X.alphaN fun i ↦ d.1.getD i 0) m₁).getD []))

/-! ## Frozen statements -/

section Frozen

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}

/-- `P_S` at M′ grinds nothing outside its query groups. -/
theorem ng_PSWithM (hm : ∀ x, (mid x).NoGrind) (x : List UInt8) : (PSWithM mid x).NoGrind :=
  ng_PSWithMH hm x

/-- **`P_S` at M′ in the invariant**: from the empty history, every group at most `εS`, lead `0`; an accepting
return has `ExtIM`. With `Good := ⊥` this is soundness. -/
noncomputable def psInvM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (x : List UInt8) :
    Spec (PSWithM mid x) (fun h ↦ h = []) (fun b h ↦ b = true → ExtIM mid Good x h) εS 0 0 :=
  (Spec.bind' (rootInvM hLm) fun _ ↦
    Spec.bind' (((hmid x εS le_rfl).some.traced
        (fun h ↦ (commitRootUd cfgMain24G).after h = some (.ret ()))).mono (fun _ h ↦ h) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl)
      fun cl ↦ (mainOpenInv (Gd := Good x) (M := ExtIM mid Good x) (J := RunMidM mid x cl)
        (fun _ l h ↦ h.append l)
        (fun a h₀ l hr ha hg ↦ ⟨h₀ ++ l, cl, a, List.prefix_refl _, mainPrefixProg_afterM hr ha, hg⟩)).mono
        (fun h ⟨⟨hcand, ⟨W, hc, hW⟩, hma, hlen⟩, hrun⟩ ↦
          ⟨⟨⟨by decide, by rw [hc]; rfl, ⟨W, by rw [hc]; rfl, hW⟩, hcand⟩, hma, hlen⟩, hrun⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).congr rfl

/-- **M′'s good residual, unfolded** (as `goodRes_rec20Jp`, three levels): a good root candidate `q`, a member
`V₁` of level 1's list on `q`'s path after `α₀`, a member `V₂` of level 2's list on `q`'s path after
`α₀ ++ α₁`, and the residual is `q`'s path after `α₀ ++ α₁ ++ α₂`. -/
theorem goodRes_main23Jq {G : LeanVM.Protocol.Column CMain.nu20 → Prop} {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)}
    {r : WhirStateT × List E} {res : List E} (α₀ : Fin 6 → E) (α₁ α₂ : Fin 4 → E)
    (hfs : r.1.folds = List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂)
    (hG : GoodRes (codesMain23Jq 2) 2
      (gdFinal codesMain23Jq cs r.1.folds 0 0 (cfgMain23Jq 1).levels (gdRoot (codesMain23Jq 0) G cs))
      r res cs) :
    ∃ q ∈ Candidates CMain.nu20 2 (codesMain23Jq 0).thr (wordOf cs 0), G q ∧
      (∃ V₁ ∈ iList (codesMain23Jq 1).code (codesMain23Jq 1).thr (rowsOf 4 (laneO 1 cs (codesMain23Jq 1).n)),
        PathAt q (List.ofFn α₀) (decode (codesMain23Jq 1) V₁)) ∧
      (∃ V₂ ∈ iList (codesMain23Jq 2).code (codesMain23Jq 2).thr (rowsOf 4 (laneO 2 cs (codesMain23Jq 2).n)),
        PathAt q (List.ofFn α₀ ++ List.ofFn α₁) (decode (codesMain23Jq 2) V₂)) ∧
      (∀ y : Fin (codesMain23Jq 2).κ → Bool,
        resMsg res y = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ List.ofFn α₂ ++ bitsL y)) :=
  goodRes_main23JqH α₀ α₁ α₂ hfs hG

/-- **M′'s extraction** (luck over `C_main`'s three lists, `≤ 2^-132` per group; the map `extSM`). -/
noncomputable def extJM (hsh : MidShapeM mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : List UInt8 → List BF64 → Signed} (hnode : NodeSoundM VS vk Good child) : ExtJM mid Good VS vk := by
  exact
    { BL := LuckBM mid
      BL_nil := fun _ ↦ not_luckBM_nil
      BL_read := fun _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_commit := fun _ _ _ _ hB ↦ not_luckBM_snoc rfl hB
      BL_group := fun {_ h p} _ _ _ _ hB ↦ (esc_luckBM_le_132 p h hB).trans coe_εB.ge
      ext := extSM mid child
      extract := fun {c x _} hok hreach _ hE hB _ ↦ by
        obtain ⟨h₁, cl, ⟨ρ, r, res⟩, ⟨t, rfl⟩, hpre, hg⟩ := hE
        obtain ⟨q, hq, hdec⟩ := decode_SMH (hsh.noCommit x) hpre hg (reachable_commit_ws hreach) hB
        have hd : mainDataM mid x (h₁ ++ t) = some (r.1.folds, res) := by
          unfold mainDataM
          rw [VerifierProgram.retSplit_of_after _ _ _ hpre]
        dsimp only at hdec
        unfold extSM
        rw [hd, Option.bind_some]
        dsimp only
        rw [hdec, Option.getD_some]
        exact hnode c x q hok hq }

/-- **`extJM`'s map is the decoder chain** (no choice). -/
theorem extJM_ext (hsh : MidShapeM mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : List UInt8 → List BF64 → Signed} (hnode : NodeSoundM VS vk Good child) :
    (extJM hsh hnode).ext = extSM mid child := by
  rfl

end Frozen

/-! ## Assembly -/

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}
  {VS : SProg} {vk : RecursionFast.Digest}

/-- **The knowledge certificate of the `S` branch at M′**: no doom, luck `¬ Inv ∨ BL` at
`εB = 7·2^-131 + 2^-132`. -/
noncomputable def kcertSM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : KCert (schemeS vk (PSWithM mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeS vk (PSWithM mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtIM mid Good)
    (fun x ↦ (psInvM hmid hLm hsh x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWithM hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : Scheme.εFS (kcertSM hmid hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **M′'s open obligations** (as `OpenS`): the middle phases on `C_main` only, `NodeSoundM`, the refinement of
`V_S` to `PSWithM`, the executable extractor on good logs. -/
structure OpenSM (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecM mid Good εS Lm
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSM hmid hLm hsh (extJM hsh (hnode vk))) L < 1 →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWithM mid)).Ex (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext c π L

/-- **`SSound` from M′'s open obligations.** -/
theorem sSound_of_openSM {E : Digest → Proof → Log → Option Wit} (o : OpenSM VS E) (vk : Digest) :
    SSound VS E vk :=
  sSound_of VS E vk (PSWithM o.mid) (kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk)))
    (εFS_kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk))) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

/-! ## Stage formats (lvm2 E2F): the scheme with a static width per read and the stage's sizes -/

/-- **A stage's proof format** (lvm2 E2F; every stage-specific number of the `S` branch's scheme): the read
widths `rw` (the `n`-th read takes `rw n` bytes; `eOfBytes` zero-pads: 8 B nonces, 16 B `E2` scalars, 24 B `E`
scalars), the proof's size `pz`, the header's bytes `hb` (the statement is bytes `8 … hb - 1`), and the occupied
words `occ` of each commitment shape. -/
structure SFmt where
  rw : ℕ → ℕ
  rw_pos : ∀ n, 0 < rw n
  pz : ℕ
  hb : ℕ
  occ : ℕ → ℕ → ℕ

/-- **The header parser of a format**: a proof of `pz` bytes starting `'S' 0^7` is the statement (bytes
`8 … hb - 1`) and the body. -/
def hdrSW (pz hb : ℕ) (π : Proof) : Option (List UInt8 × List UInt8) :=
  if π.size = pz ∧ π.data.toList.take 8 = sPrefix then
    some ((π.data.toList.drop 8).take (hb - 8), π.data.toList.drop hb)
  else none

/-- **The `S` branch's scheme at a format**: `schemeS` with the format's header, read widths and occupied words.
The only fact asked of the widths is `0 < rw n` (an empty message reads openings only); the forest's reading stays
deterministic since a read's index is its history's (`nReads`), so no length rule is needed. -/
def schemeSW (f : SFmt) (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) : Scheme :=
  { schemeS vk P with hdr := hdrSW f.pz f.hb, occ := f.occ, rw := f.rw, rw_pos := f.rw_pos }

/-- **M′'s format** (S2GM): 24 bytes per read, `|π| = piSz`, `headerBytes` of header, `occOfS`. -/
def fmtM : SFmt := ⟨fun _ ↦ 24, fun _ ↦ by decide, piSz, Lvm.headerBytes, occOfS⟩

/-- **`schemeS` is the scheme at M′'s format.** -/
theorem schemeSW_fmtM (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    schemeSW fmtM vk P = schemeS vk P := rfl

/-- **`SSound` from a knowledge certificate of `schemeSW f`** (as `sSound_of`). -/
theorem sSound_ofW (f : SFmt) (VS : SProg) (E : Digest → Proof → Log → Option Wit)
    (vk : Digest) (P : List UInt8 → VerifierProgram Bool) (K : KCert (schemeSW f vk P) (Rel (accV VS vk)))
    (hε : Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128)
    (refines : ∀ L c π, isS π = true → (VS vk c π).runLog L = some true →
      ((schemeSW f vk P).V c π).runLog L = some true)
    (ext_eq : ∀ L c π, isS π = true → L.length ≤ logCap → Lvm.FS.Scheme.μ K L < 1 →
      ((schemeSW f vk P).V c π).runLog L = some true →
      (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨ E c π L = (schemeSW f vk P).Ex K.ext c π L) :
    SSound VS E vk :=
  ⟨schemeSW f vk P, K, hε, refines, ext_eq⟩

section W

variable (f : SFmt)

/-- **`kcertSM` at a format** (the certificate does not look at the format). -/
noncomputable def kcertSMW (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : KCert (schemeSW f vk (PSWithM mid)) (Rel (accV VS vk)) :=
  kcertOfInv (S := schemeSW f vk (PSWithM mid)) (εI := 7 * (2 : ℝ≥0)⁻¹ ^ 131) (εL := (2 : ℝ≥0)⁻¹ ^ 132)
    (Ext := ExtIM mid Good)
    (fun x ↦ (psInvM hmid hLm hsh x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl)
    zero_le (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWithM hsh.noGrind x) hr)
    X.BL X.BL_nil X.BL_read X.BL_commit X.BL_group
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) X.ext X.extract

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSMW (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : Scheme.εFS (kcertSMW f hmid hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **M′'s open obligations at a format** (`OpenSM` with `schemeSW f`). -/
structure OpenSMW (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecM mid Good εS Lm
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeSW f vk (PSWithM mid)).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))) L < 1 →
    ((schemeSW f vk (PSWithM mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeSW f vk (PSWithM mid)).Ex (kcertSMW f hmid hLm hsh (extJM hsh (hnode vk))).ext c π L

/-- **`SSound` from M′'s open obligations at a format.** -/
theorem sSound_of_openSMW {E : Digest → Proof → Log → Option Wit} (o : OpenSMW f VS E) (vk : Digest) :
    SSound VS E vk :=
  sSound_ofW f VS E vk (PSWithM o.mid) (kcertSMW f o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk)))
    (εFS_kcertSMW f o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk))) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

end W

end Lvm.ASM
