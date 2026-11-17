-- New for lvm2 sigma_LEAF (SLF-K, 2026-11-16): S2GU's extractor window (`loU`, `sIdxU`, `winWU20`, the pair form
-- `nodeML_of_pairU`) and S2GU's leaf lengths (`leafLensU`), moved verbatim out of `LvmS2GUCert`/`LvmS2GUXS` so that
-- the S2GL and S2GS certificates import them without S2GU's instance chain (`LvmS2GUStmt`, `LvmS2GUXS`, `LvmS2GUCert`).
import LvmS2GUMid

/-!
# S2GU's extractor window, shared (D-WIN (B))

* `leafLensU` (`Lvm.XS`): `C_main`'s root row of 46 words (368 B), the later levels' 384 B.
* `loU`, `loU_le`, `sIdxU`, `winWU20`, `nodeML_of_pairU` (`Lvm.CT`): the window's first lane, the stream word's index in
  the window, the window holds the stream block `recBU20`, `NodeSoundML` from the pair form.
-/

set_option autoImplicit false

namespace Lvm.XS

/-- **S2GU's leaf lengths**: `C_main`'s root row of 46 words (368 B), the later levels' 384 B (`Lvm.X.leafLens`
is S2GM's/S2GT's `[376, 384]`). -/
def leafLensU : List ℕ := [368, 384]

end Lvm.XS

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped Lvm.E2F Lvm.E2V Lvm.XS Lvm.E2Q Lvm.E2U
open LeanVM.Protocol LeanVM.Protocol.Verifier

/-- **The window's first lane for the statement `x`** at S2GU: `32` when small (the stream at physical lane 32), M′'s
`winLo` (`40`) when big. -/
def loU (x : List UInt8) : ℕ := if Lvm.Shape.small x then 32 else Lvm.X.winLo

theorem loU_le (x : List UInt8) : loU x + Lvm.X.winC ≤ 64 := by unfold loU; split <;> decide

/-- Stream word `i` (`i < 2^19`) of the statement's shape at S2GU, as an index into its window: the stream starts the
window (small: physical word `2i` from lane 32; big: word `i` from lane 40). -/
def sIdxU (x : List UInt8) (i : ℕ) : ℕ := if Lvm.Shape.small x then 2 * i else i

/-- The window from lane `loU x` holds the stream block (both shapes; `bigOf` in the small shape). -/
theorem winWU20 (x : List UInt8) (q : Column CMain.nu20) :
    (fun i ↦ if i < 2 ^ 19 then BF64.toBitVec ((Lvm.X.winOfL (loU x) q).getD (sIdxU x i) 0) else BF64.toBitVec 0) =
      Lvm.NS.wOfCol (recOfU20 x q) := funext fun i ↦ by
  rw [wOfCol_eq, show recOfU20 x q = recBU20 (Lvm.Shape.view x q) from rfl]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, getD_recBU20 _ hi]
    refine congrArg BF64.toBitVec ?_
    unfold sIdxU loU Lvm.Shape.view Lvm.X.winOfL Lvm.X.msgOfN
    cases hs : Lvm.Shape.small x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by simp only [Lvm.X.winC]; omega)]
      simp only [Option.map_some, Option.getD_some, CMain.sOffU20, Lvm.X.winLo]
      norm_num
    · simp only [↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by simp only [Lvm.X.winC]; omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [Lvm.Shape.getD_bigOf q (by simp only [CMain.sOffU20, CMain.nu20]; omega),
        show CMain.sOffU20 + i = 4 * 2 ^ 20 + (1 * 2 ^ 20 + i) by simp only [CMain.sOffU20]; omega,
        Lvm.Shape.bigWord_hi q (by norm_num) (by omega), Lvm.NS.wd]
      exact congrArg (fun k ↦ q.values.getD k 0) (by omega)
  · rw [ite_eq_right hi, getD_recBU20_ge _ (by omega)]

/-- **`NodeSoundML` at S2GU from the pair form** (`nodeM_of_pair` at the stream block `recBU20` and the window
`loU`). -/
theorem nodeML_of_pairU {VS : SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {childW : List UInt8 → List BF64 → Signed} {child : Column 19 → Signed}
    (hch : ∀ x q, childW x (Lvm.X.winOfL (loU x) q) = child (recOfU20 x q))
    (hnode : NodeSound VS vk (fun x qm qr ↦ G x qm qr ∧ SBlkU qm qr) child) :
    NodeSoundML loU VS vk (GoodOfM recOfU20 (Lvm.Shape.Good₂ G)) childW := fun c x q hok hG ↦ by
  rw [hch]
  exact hnode c x (Lvm.Shape.view x q) (recBU20 (Lvm.Shape.view x q)) hok ⟨hG, sBlkU_recBU20 _⟩

end Lvm.CT
