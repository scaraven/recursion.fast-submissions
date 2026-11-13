-- New for lvm2 (J2C-C, J2′): extraction under the INV certificate (J2C-DES §1 "Extraction", §3 T7–T8). The
-- deliverable `extJ` is stated at G0 by the lead; its construction is J2C-C's. The extraction map `extSJ` is
-- `LvmCertSExt.extS` (WP-14 / X-REC2) on J2′'s reader `recData2J`; its correctness follows `decode_S` with
-- J2P-L's `goodRes_rec20Jp`/`j_extract2` in place of the UD doom facts.
import LvmCertSExt
import LvmCertSInv
import LvmCertSJ
import LvmCertSExtJSplit
import LvmWhirGoodJp

/-!
# Extraction at J2′ (J2C-DES §3, T7–T8)

**`extJ`**: the extraction interface `ExtJ mid Good VS vk` (`LvmCertSInv`) for `P_S` at J2′, from the middle
phases' shape and `NodeSound`:
* the luck `LuckBJ` (`LvmCertSLuckJ`: level-0 luck over the root's Johnson candidates, level-1 luck over
  `iList codeJ9R3`), group bound `≤ 2^-132` (`esc_luckJ_le_132`);
* the map **`extSJ mid child`**: the decoder chain on the history, **`recData2J` → `decodeRec1` →
  `decodeRec`** (DEC's level-1 decoder on `C_rec`'s level-1 word, `α₁` and the residual, then WP-13b's
  level-0 decoder on the root word, `α₀` and the level-1 output), as `extS`; no choice.
  `extJ_ext`: `(extJ hsh hnode).ext = extSJ mid child` (`rfl`);
* **`decode_SJ`** (T7–T8): at a reachable history with `ExtI` and not lucky, both decoders succeed and return
  the message of a `GoodRec` candidate `q`: `ExtI`'s prefix is a completed `recPrefixProg` run
  (`recPrefix_split`), its residual is good (`goodRes_rec20Jp`: a good root candidate `q` at
  `(codesRec20Jp 0).thr`, a level-1 list member `V` on `q`'s path after `α₀`, the residual on `q`'s path after
  `α₀ ++ α₁`), `j_extract2`'s path lemmas give the decoders' relations, and off the luck
  `decodeRec1_of_partsJ` and `decodeRec_of_mem` (any list member, `A ≥ 2^9`, `A ≥ 2^13`) return `V`'s and
  `q`'s messages;
* `codesRec20_one_code`: the UD level-1 code of `C_rec` is `codeJ9R3`'s (`decodeRec1_of_ud` is stated at
  `codesRec20 1`; `decodeRec1_of_partsJ` uses it by definitional unfolding).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped NNReal ENNReal

/-! ## The level-1 code -/

/-- **`C_rec`'s UD level-1 code is J2′'s** (`κ = 9`, `R = 3`; only the threshold differs). -/
theorem codesRec20_one_code : (codesRec20 1).code = codeJ9R3.code := rfl

/-- **DEC's level-1 decoder returns any member of J2′'s level-1 list** (`decodeRec1_of_ud` at
`A = codeJ9R3.thr = 1451 ≥ 2^9`, the same code), the membership in its two parts. -/
theorem decodeRec1_of_partsJ (W₁ : Compile.Word) (hW : ∀ v < 2 ^ 12, (W₁ v).length = 48)
    (α₁ : Fin 4 → E) (f₂ : (Fin (codesRec20Jp 1).κ → Bool) → E)
    (V : (Fin 4 → Bool) → Fin (codesRec20Jp 1).n → E)
    (hcw : IsInterleavedCodeword (codesRec20Jp 1).code V)
    (hcl : IsClose (codesRec20Jp 1).thr (rows1 4 (codesRec20Jp 1).n W₁) V)
    (hf : f₂ = ∑ u, eqW α₁ u • decode (codesRec20Jp 1) V u)
    (hL : ¬ FoldAllLuck α₁ (rows1 4 (codesRec20Jp 1).n W₁) V) :
    Lvm.X.decodeRec1 (Lvm.X.wdOf W₁) (Lvm.X.alphaN1 α₁) (Lvm.X.fN2 f₂) =
      some (Lvm.X.fNr (joinMsg (by rfl : 19 - LeanVM.Protocol.EndToEnd.laneBits = 4 + (codesRec20Jp 1).κ)
        (decode (codesRec20Jp 1) V))) :=
  Lvm.X.decodeRec1_of_ud W₁ hW α₁ f₂ V hcw (A := 1451) (by norm_num) hcl hf hL

/-! ## The extraction map -/

/-- **J2′'s extraction map**: DEC's level-1 decoder on `C_rec`'s level-1 word, level-1 fold challenges and
residual, then WP-13b's level-0 decoder on the root word, the level-0 fold challenges and the level-1
output, all read off the history by `recData2J`; the witness with the decoded column's child. -/
noncomputable def extSJ (mid : List UInt8 → VerifierProgram OpenClaims)
    (child : Column 19 → Signed) (_c : RecursionFast.Digest) (x : List UInt8) (h : List Ev) : Wit :=
  witOf x (child (colOf ((recData2J mid x h).bind fun d ↦
    (Lvm.X.decodeRec1 (Lvm.X.wdOf (Wr1Of h)) (Lvm.X.alphaN1 fun i ↦ d.2.1.2.getD i 0)
        (Lvm.X.fN2 (resMsg d.2.2))).bind fun m ↦
      Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ d.1.getD i 0) m)))

/-- A list of length `n` is the `ofFn` of its `getD`. -/
theorem ofFn_getD_eq {n : ℕ} (l : List E) (hl : l.length = n) :
    List.ofFn (fun i : Fin n ↦ l.getD i 0) = l := by
  subst hl
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

/-- **A list member in its two parts**, generic in the instances: `ConsAt`'s list (`LvmWhirPathR`) and the
decoders' lists are elaborated with different `Fintype` instances on the rows, so the membership is passed
through its parts (`IsInterleavedCodeword`, `IsClose`), which carry no instance. -/
theorem exists_iList_parts {F ι ρ : Type} [Field F] [Fintype F] [Fintype ι] [Fintype ρ]
    {C : Submodule F (ι → F)} {A : ℕ} {O : ρ → ι → F} {P : (ρ → ι → F) → Prop}
    (h : ∃ U ∈ iList C A O, P U) : ∃ U, (IsInterleavedCodeword C U ∧ IsClose A O U) ∧ P U := by
  obtain ⟨U, hU, hp⟩ := h
  exact ⟨U, (mem_iList _ _ _ _).1 hU, hp⟩

section Extract

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {x : List UInt8}

/-- **The decoders succeed at J2′** (J2C-DES T7–T8): at a reachable history of `P_S` with `ExtI` and not
lucky, `recData2J` reads `C_rec`'s values, DEC's level-1 decoder returns a message `m`, and WP-13b's decoder
on the root word, `α₀` and `m` returns the message of a `GoodRec` candidate `q`. -/
theorem decode_SJ (hsh : MidShape mid) {h : List Ev} (hreach : (PSWith mid x).Reachable h)
    (hE : ExtI mid Good x h) (hB : ¬ LuckBJ mid x h) :
    ∃ q, GoodRec Good x q ∧ ∃ d, recData2J mid x h = some d ∧ ∃ m,
      Lvm.X.decodeRec1 (Lvm.X.wdOf (Wr1Of h)) (Lvm.X.alphaN1 fun i ↦ d.2.1.2.getD i 0)
        (Lvm.X.fN2 (resMsg d.2.2)) = some m ∧
      Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ d.1.getD i 0) m =
        some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
  obtain ⟨h₁, cl, a, ⟨t, rfl⟩, hpre, hG⟩ := hE
  obtain ⟨hr, lm, ρ, lq, quad, lf, r, lc, lz, z, ly, y, lhy, hy, lg, g, lhq, hq, lf1, r₁, lres, res,
    hh₁, rfl, h1, h3, h8, h10, hc, hz, hyr, hhy, hg, hhq, hf1, hres⟩ := recPrefix_split hpre
  obtain ⟨W₁, rfl⟩ := readCommitment_after hc
  obtain ⟨Wm, W₀, rfl⟩ := roots_after h1
  -- the fold states: `α₀ = r.2`, `α₁ = r₁.2`, all folds `α₀ ++ α₁`
  have hrd := recData2J_split hpre h10 hf1 t
  obtain ⟨hfl1, hlen6, hlen4⟩ := folds_splitJ h10 hf1
  set α₀ : Fin LeanVM.Protocol.EndToEnd.laneBits → E := fun i ↦ r.2.getD i 0 with hα₀
  set α₁ : Fin 4 → E := fun i ↦ r₁.2.getD i 0 with hα₁
  have hfs : r₁.1.folds = List.ofFn (α₀ : Fin 6 → E) ++ List.ofFn α₁ := by
    rw [hfl1, ofFn_getD_eq _ hlen6, ofFn_getD_eq _ hlen4]
  -- the commitments
  set ht := 19 - r.1.folds.length - 4 + 3
  have hcs : commits h₁ = [(19, 64, Wm), (15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
    rw [hh₁]
    simp only [commits_append, NoCommit.after_commits (hsh.noCommit x) h3,
      NoCommit.after_commits (nc_roundPoly _ _ _) h8, NoCommit.after_commits (nc_foldRoundsT _ _ _) h10,
      NoCommit.after_commits (nc_sampleChallenges _) hz,
      NoCommit.after_commits (p := readScalar) nc_readScalar hyr,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhy, NoCommit.after_commits (nc_qgRecJ _) hg,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhq, NoCommit.after_commits (nc_foldRoundsT _ _ _) hf1,
      NoCommit.after_commits (nc_readScalars _) hres, List.nil_append, List.append_nil]
    rfl
  have hview : viewC 1 2 (commits h₁) = [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by rw [hcs]; rfl
  -- the good residual (`ExtI`'s), unfolded
  have hG' : GoodRes (codesRec20Jp 1) 1 (gdFinal codesRec20Jp [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)]
      r₁.1.folds 0 0 cfgRec20Jp.levels (gdRoot (codesRec20Jp 0) (GoodRec Good x)
        [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)])) r₁ res [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
    have := hG
    simp only [GoodResAt] at this
    rw [hview] at this
    exact this
  obtain ⟨q, hq0, hgood, hcons, hresq⟩ := goodRes_rec20Jp α₀ α₁ hfs hG'
  have hrows : rowsOf 4 (laneO 1 [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] (codesRec20Jp 1).n) =
      rows1 4 (codesRec20Jp 1).n W₁ := rfl
  rw [hrows] at hcons
  obtain ⟨V, hVm, hpath⟩ := exists_iList_parts hcons
  -- `j_extract2`'s relations (its membership argument is not needed for these two)
  have hjoin : joinMsg (by rfl : 19 - LeanVM.Protocol.EndToEnd.laneBits = 4 + (codesRec20Jp 1).κ)
      (decode (codesRec20Jp 1) V) = foldMsg α₀ q :=
    (pathAt_zero_iff_foldMsg q α₀ _).mp ((pathAt_joinMsg_iff _ q _ _).mpr hpath)
  have hf₂ : resMsg res = ∑ u, eqW α₁ u • decode (codesRec20Jp 1) V u :=
    funext fun y ↦ by rw [hresq y, sum_eqW_path q _ α₁ _ hpath y]
  -- the history's words and readers
  subst hh₁
  have hws := reachable_commit_ws hreach
  have hW₀ : WellShaped 64 W₀ := hws 15 64 W₀ (by simp)
  have hW₁ : WellShaped (3 * 2 ^ 4) W₁ := hws ht _ W₁ (by simp)
  have hWr : WrOf ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++ (lq ++
      (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lz ++ (ly ++ (lhy ++ (lg ++ (lhq ++ (lf1 ++ lres))))))))))) ++ t) =
      W₀ := by
    unfold WrOf
    rw [List.append_assoc, rootsOf_split h1]
    rfl
  have hWr1 : Wr1Of ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++ (lq ++
      (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lz ++ (ly ++ (lhy ++ (lg ++ (lhq ++ (lf1 ++ lres))))))))))) ++ t) =
      W₁ := by
    unfold Wr1Of
    rw [commits_append, hcs]
    rfl
  have hfc0 := foldChal_of_splitJ (R := [Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lz ++ (ly ++ (lhy ++ (lg ++
    (lhq ++ (lf1 ++ lres)))))) ++ t) h1 h3 h8 h10
  have hfc1 := foldChal1J_of_splitJ (R' := lres ++ t) (lc := [Ev.commit ht (3 * 2 ^ 4) W₁]) h1 h3 h8 h10 rfl hz hyr hhy hg hhq hf1
  have hW1L := W1L_of_splitJ (R := lz ++ (ly ++ (lhy ++ (lg ++ (lhq ++ (lf1 ++ (lres ++ t))))))) h1 h3 h8 h10
    (rfl : [Ev.commit ht (3 * 2 ^ 4) W₁] = _)
  simp only [List.append_assoc] at hrd hfc0 hfc1 hW1L hWr hWr1 hB ⊢
  rw [hWr, hWr1]
  -- no luck
  have hl0 : ¬ FoldAllLuck α₀ (laneRows 19 2 W₀) (encRows 19 2 q) := by
    intro hFL
    refine hB (.inl ⟨q, ?_, ?_⟩)
    · rw [hWr]; exact hq0
    · rw [foldChalJ, hfc0, hWr]
      exact roundsLuck_of_foldAllLuck _ _ _ _ hlen6 hFL
  have hl1 : ¬ FoldAllLuck α₁ (rows1 4 (codesRec20Jp 1).n W₁) V := by
    intro hFL
    refine hB (.inr (luckB1J_of_parts (V := V) ?_ ?_ ?_))
    · exact hVm.1
    · rw [hW1L]; exact hVm.2
    · rw [hW1L, hfc1]
      exact roundsLuck_of_foldAllLuck _ _ _ _ hlen4 hFL
  -- the decoders
  have hdec1 := decodeRec1_of_partsJ W₁ (fun v _ ↦ hW₁ v) α₁ (resMsg res) V hVm.1 hVm.2 hf₂ hl1
  rw [hjoin] at hdec1
  have hdec := Lvm.X.decodeRec_of_mem W₀ α₀ q (fun v _ ↦ hW₀ v) hq0
    (by show 2 ^ 13 ≤ 16410; norm_num) hl0
  exact ⟨q, hgood, _, hrd, _, hdec1, hdec⟩

/-- **The extraction is a witness at J2′**: at a reachable accepted history with `ExtI` and not lucky,
`extSJ` gives a witness of the relation. -/
theorem extract_SJ (hsh : MidShape mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : Column 19 → Signed} (hnode : NodeSound VS vk Good child) {c : RecursionFast.Digest}
    {h : List Ev} (hok : okS vk c x = true) (hreach : (PSWith mid x).Reachable h)
    (hE : ExtI mid Good x h) (hB : ¬ LuckBJ mid x h) :
    Rel (accV VS vk) c (extSJ mid child c x h) := by
  obtain ⟨q, ⟨qm, hG⟩, d, hrd, m, hdec1, hdec⟩ := decode_SJ hsh hreach hE hB
  unfold extSJ
  rw [hrd, Option.bind_some]
  rw [hdec1, Option.bind_some, hdec, colOf_msgOf]
  exact hnode c x qm q hok hG

end Extract

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel}

/-- **J2′'s extraction** (J2C-DES §1): the luck `LuckBJ` and the decoders' map `extSJ`, extracting from
`ExtI`. -/
noncomputable def extJ (hsh : MidShape mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : LeanVM.Protocol.Column 19 → Signed} (hnode : NodeSound VS vk Good child) : ExtJ mid Good VS vk where
  BL := LuckBJ mid
  BL_nil _ := LuckBJ_nil
  BL_read _ _ _ hB := not_luckBJ_snoc rfl hB
  BL_commit _ _ _ _ hB := not_luckBJ_snoc rfl hB
  BL_group {_ h p} _ _ _ _ hB := (esc_luckJ_le_132 p h hB).trans coe_εB.ge
  ext := extSJ mid child
  extract hok hreach _ hE hB _ := extract_SJ hsh hnode hok hreach hE hB

/-- **`extJ`'s map is the decoder chain** `recData2J` → `decodeRec1` → `decodeRec` (no choice). -/
theorem extJ_ext (hsh : MidShape mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : LeanVM.Protocol.Column 19 → Signed} (hnode : NodeSound VS vk Good child) :
    (extJ hsh hnode).ext = extSJ mid child := rfl

end Lvm.ASM
