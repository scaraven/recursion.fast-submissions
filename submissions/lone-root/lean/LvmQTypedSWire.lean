-- New for lvm2 (roll 8 = B1, B1-IX-S): the typed V_S's start-up. `Φ_Q`'s class check on the fast entries
-- (`K.FLF`, `LvmWiringKD`), equal to `PhiCache.okB`, and `deriveTerms`' value on the fast entries.
import LvmWiring

/-!
# The class check on the fast entries

`K.FL.rowEnts` recomputes `Block.tw` (a sum over the template) at every entry; `K.FLF` caches it per block. Here:

* **`flf_srcEnts`**: `FLF`'s entries are `FL`'s, at every row and iteration (no hypothesis);
* **`checkTermsF_eq`**: `K.checkTermsF = K.checkTerms` (both are `K.checkTermsG` on equal entry functions);
* **`PhiCache.okBF`**, **`okBF_eq`**: `PhiCache.okB` with `checkTermsF`; it *is* `okB`, so the guard's check
  gives `PhiQC_eq`'s `hc` unchanged;
* **`deriveTerms_eq`**: `K.deriveTerms` (on `FLF`'s entries) is `K.deriveTermsG` on `FL`'s, the original algorithm.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

namespace K

theorem sw_getD_map {α : Type} [Inhabited α] (a : Array α) (f : α → ℕ) (hf : f default = 0) (b : ℕ) :
    (a.map f).getD b 0 = f (a.getD b default) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[b]? with
  | none => exact hf.symm
  | some x => rfl

theorem sw_tw_default (τ : Ty) : (default : Block).tw τ = 0 := rfl

theorem bsRec_eq (a : Array (ℕ × ℕ × ℕ)) (n : ℕ) : ∀ (g lo hi : ℕ), FL.bsRec a n lo hi g = fl_bsLoop a n lo hi g
  | 0, lo, hi => by rw [fl_bsLoop_eq]; simp [FL.bsRec]
  | g + 1, lo, hi => by
    rw [fl_bsLoop_eq]
    unfold FL.bsRec
    by_cases h : lo < hi
    · simp only [h, true_and, Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel, bsRec_eq a n g]
    · simp [h]

theorem ownerF_eq (F : FL) : F.ownerF = F.owner := by
  funext τ n
  rw [fl_owner_bs]
  exact bsRec_eq _ n _ 0 _

theorem wordKF_eq (F : FL) : F.wordKF = F.wordK := by
  funext n
  unfold FL.wordKF FL.wordK
  rw [ownerF_eq]

theorem wordE3_eq (F : FL) (n : ℕ) : F.wordE3 n = (F.wordE n 0, F.wordE n 1, F.wordE n 2) := by
  unfold FL.wordE3 FL.wordE
  rw [ownerF_eq, wordKF_eq]
  cases F.owner .E n with
  | none => rfl
  | some b =>
    dsimp only
    generalize ((F.srcEA.getD b #[]).getD ((n - (F.bl.getD b default).stE) % (F.bl.getD b default).twE) default) = cs
    cases cs <;> rfl

theorem cellEntsF_eq (F : FL) : F.cellEntsF = F.cellEnts := by
  funext τ n w
  cases τ with
  | K => simp only [FL.cellEntsF, FL.cellEnts, wordKF_eq]
  | E => simp only [FL.cellEntsF, FL.cellEnts, wordE3_eq]

/-- **`FLF`'s entries are `FL`'s.** -/
theorem flf_rowEnts (Q : Program) (lay : Lay) (b t jf : ℕ) :
    (FLF.ofLay Q lay).rowEnts b t jf = (FL.ofLay Q lay).rowEnts b t jf := by
  have hK : (FLF.ofLay Q lay).twK.getD b 0 = ((FL.ofLay Q lay).qb.getD b default).tw .K :=
    sw_getD_map _ _ (sw_tw_default .K) b
  have hE : (FLF.ofLay Q lay).twE.getD b 0 = ((FL.ofLay Q lay).qb.getD b default).tw .E :=
    sw_getD_map _ _ (sw_tw_default .E) b
  unfold FLF.rowEnts FL.rowEnts
  rw [hK, hE]
  simp only [cellEntsF_eq]
  rfl

theorem flf_srcEnts (Q : Program) (lay : Lay) : (FLF.ofLay Q lay).srcEnts = (FL.ofLay Q lay).srcEnts := by
  funext s jf
  cases s with
  | row b t => exact flf_rowEnts Q lay b t jf
  | aux k r =>
    show (FLF.ofLay Q lay).auxEnts k r jf = (FL.ofLay Q lay).auxEnts k r jf
    unfold FLF.auxEnts FL.auxEnts
    simp only [cellEntsF_eq]
    rfl

/-- `checkTerms` is `checkTermsG` on `FL`'s entries. -/
theorem checkTerms_eqG (Q : Program) (lay : Lay) (ts : Array CTerm) :
    checkTerms Q lay ts = checkTermsG (FL.ofLay Q lay).srcEnts ts := rfl

theorem checkTermsG_eqA (ents : TSrc → ℕ → List Ent) (ts : Array CTerm) :
    checkTermsG ents ts = checkTermsGA (fun s jf ↦ (ents s jf).toArray) CTerm.at ts := rfl

theorem affAtGo_eq (jf : ℕ) : ∀ (cs : List ℕ) (i : ℕ),
    affAtGo jf cs i = ((List.range cs.length).map fun k ↦ if jf.testBit (i + k) then cs.getD k 0 else 0).sum
  | [], _ => rfl
  | c :: cs, i => by
    rw [affAtGo, affAtGo_eq jf cs (i + 1), List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
      List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, List.getD_cons_succ]
    rw [show i + (k + 1) = i + 1 + k by omega]

/-- **`Aff.atF` is `Aff.at`.** -/
theorem aff_atF : Aff.atF = Aff.at := by
  funext a jf
  unfold Aff.atF Aff.at
  rw [affAtGo_eq]
  simp only [Nat.zero_add]

theorem opClass_atF : OpClass.atF = OpClass.at := by
  funext c jf
  cases c <;> simp only [OpClass.atF, OpClass.at, aff_atF]

theorem cterm_atF : CTerm.atF = CTerm.at := by
  funext c jf
  simp only [CTerm.atF, CTerm.at, opClass_atF]

/-- **The check on the fast entries is the check.** -/
theorem checkTermsF_eq (Q : Program) (lay : Lay) (ts : Array CTerm) : checkTermsF Q lay ts = checkTerms Q lay ts := by
  show checkTermsGA (fun s jf ↦ ((FLF.ofLay Q lay).srcEnts s jf).toArray) CTerm.atF ts = _
  rw [cterm_atF, flf_srcEnts, checkTerms_eqG, checkTermsG_eqA]

/-- **`deriveTerms` is the original algorithm** (`deriveTermsG` on `FL`'s entries). -/
theorem deriveTerms_eq (Q : Program) (lay : Lay) :
    deriveTerms Q lay = deriveTermsG (fun s jf ↦ ((FL.ofLay Q lay).srcEnts s jf).toArray) (FL.ofLay Q lay) := by
  show deriveTermsG (fun s jf ↦ ((FLF.ofLay Q lay).srcEnts s jf).toArray) (FLF.ofLay Q lay).F = _
  rw [flf_srcEnts]
  rfl

end K

/-- The class check's key and well-formedness parts against the keys `ks` (`keysB`: `termKeys`). -/
def PhiCache.keysWith (Q : Program) (lay : Lay) (c : PhiCache) (ks : List (TSrc × ℕ)) : Bool :=
  let ls := Q.blocks.toArray.map (·.lsize)
  let srcLF : TSrc → ℕ := fun
    | .row b _ => ls.getD b 0
    | .aux k _ => (lay.aux.getD k default).l
  c.terms.map (fun t ↦ (t.src, t.idx)) == ks &&
    c.terms.all (fun t ↦ t.l == srcLF t.src && K.termWFB t)

/-- The class check's key and well-formedness parts (`PhiCache.okB` without `checkTerms`, `okB_keys`). -/
def PhiCache.keysB (Q : Program) (lay : Lay) (c : PhiCache) : Bool := c.keysWith Q lay (termKeys Q lay)

/-- `termKeys` with the templates as arrays (`termKeys` reads `(Q.blk b).tpl.getD t` per row: quadratic in the
blocks and the templates; `termKeysF_eq`). -/
def termKeysF (Q : Program) (lay : Lay) : List (TSrc × ℕ) :=
  let tps : Array (Array Row) := Q.blocks.toArray.map (·.tpl.toArray)
  ((List.range Q.blocks.length).flatMap fun b ↦
    (List.range (Q.blk b).tpl.length).flatMap fun t ↦
      (List.range (K.rowEntCount ((tps.getD b #[]).getD t default))).map (TSrc.row b t, ·)) ++
  (List.range lay.aux.length).flatMap fun k ↦
    (List.range (lay.aux.getD k default).rows.length).flatMap fun r ↦
      (List.range (entCount Q lay (.aux k r))).map (TSrc.aux k r, ·)

theorem sw_tps_getD (Q : Program) (b t : ℕ) :
    ((Q.blocks.toArray.map (·.tpl.toArray)).getD b #[]).getD t default = (Q.blk b).tpl.getD t default := by
  simp only [Program.blk, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  cases Q.blocks[b]? with
  | none => rfl
  | some B => simp

theorem termKeysF_eq (Q : Program) (lay : Lay) : termKeysF Q lay = termKeys Q lay := by
  unfold termKeysF termKeys rowsOf
  dsimp only
  rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  · congr 1
    funext b
    rw [List.flatMap_map]
    congr 1
    funext t
    simp only [entCount, sw_tps_getD]
  · congr 1
    funext k
    rw [List.flatMap_map]

/-- `keysB` on `termKeysF` (`keysBF_eq`). -/
def PhiCache.keysBF (Q : Program) (lay : Lay) (c : PhiCache) : Bool := c.keysWith Q lay (termKeysF Q lay)

theorem PhiCache.keysBF_eq (Q : Program) (lay : Lay) (c : PhiCache) : c.keysBF Q lay = c.keysB Q lay := by
  unfold PhiCache.keysBF PhiCache.keysB
  rw [termKeysF_eq]

theorem PhiCache.okB_keys (Q : Program) (lay : Lay) (c : PhiCache) :
    c.okB Q lay = (c.keysB Q lay && K.checkTerms Q lay c.terms.toArray) := by
  unfold PhiCache.okB PhiCache.keysB PhiCache.keysWith
  rfl

/-- **The class check with `FLF`'s entries** (`PhiCache.okB` with `K.checkTermsF`). -/
def PhiCache.okBF (Q : Program) (lay : Lay) (c : PhiCache) : Bool :=
  c.keysB Q lay && K.checkTermsF Q lay c.terms.toArray

/-- **`okBF` is `okB`.** -/
theorem PhiCache.okBF_eq (Q : Program) (lay : Lay) (c : PhiCache) : c.okBF Q lay = c.okB Q lay := by
  rw [PhiCache.okBF, PhiCache.okB_keys, K.checkTermsF_eq]

end Lvm.Typed
