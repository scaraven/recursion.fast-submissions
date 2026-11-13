-- New for lvm2 roll 11 (M′, R11-C): the decoders succeed at M′ (`LvmMPCert`'s `extJM`), from a good residual and
-- no luck. Adapted from `LvmCertSExtJ.decode_SJ` (two levels of `C_rec`) to `C_main`'s three levels; the decoders'
-- correctness is `LvmMPDec`'s (`decodeMP2_of_mem`, `decodeMP1_of_mem`, `decodeMP0_of_mem`, R11-X), used as stated.
import LvmMPCertSplit
import LvmMPDec
import LvmCertSExtJ

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
