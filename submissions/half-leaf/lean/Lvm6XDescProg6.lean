-- lvm6 EXI: `DescProg6` (X8b's open input of `open6X`) from the descent's round induction (`chainD`), with the
-- front's heap facts and the concrete levels, glue and output map as named hypotheses (`DescIn`, EXF/EXG; `FinOut`,
-- EXG); `open6XI`: the extractor's fields of `Open6` with `DescProg6` and `Len6` discharged. New.
import Lvm6XIndChain
import Lvm6Len

/-!
# `DescProg6`

* **`front6St c π L`**: the extractor's state before the descent (`parseIR ; frontIR6` from the initial state);
  `preOut6 descX inp = semXIR descX (front6St …)` by definition.
* **`DescIn Φ Lv n₀`** (hypothesis, EXF + EXG): on an `S` proof of `pz6` bytes of the composed scheme whose history
  has one commitment before `N₀`, the state before the descent has `Inv`, no output, and the descent's machine inputs
  `Mach` tied to the opening's log `h.drop N₀` (the front's words and challenge pairs in the round tables, each
  level's glue from the next level's columns, level 0 leaving `n₀` columns).
* **`FinOut fin L0 n₀`** (hypothesis, EXG): from level 0's first `n₀` columns representing a level-0 tuple `U`, the
  output map writes the stack `decD U` at `colB6`, with `Inv` and no output.
* **`descProg6_of`**: `DescIn ∧ FinOut → DescProg6 Φ (descX6 Lv fin)` (`GWDc` gives `OpenSem` at `ladD`,
  `chainD` the level-0 tuple: `Back`).
* **`open6XI`**: `Open6`'s `sound`, `wBranch`, `computes`, `size` for `EX6 (descX6 Lv fin)` from `DescIn`, `FinOut`
  and the descent's structural facts (`DescOk6`, `sizeIR ≤ 2^19`; level 0 may exceed X7a's `LevelOk` lane budget).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm.T
open LeanVM.Parameters (E2)
open scoped NNReal ENNReal

/-- **The state before the descent**: the parse and the front from the initial state. -/
def front6St (c : Digest) (π : Proof) (L : Log) : St :=
  semXIR (extractorInput c π L).toArray frontIR6
    (semXIR (extractorInput c π L).toArray (parseIR pz6) (initSt (mem6 + mpwX * (extractorInput c π L).length)))

theorem preOut6_eq (descX : XIR) (c : Digest) (π : Proof) (L : Log) :
    preOut6 descX (extractorInput c π L) = semXIR (extractorInput c π L).toArray descX (front6St c π L) := rfl

/-- The descent's run is the five levels (`lvRun`), then the output map. -/
theorem semXIR_descX6 (I : Array Word) (Lv : ℕ → LevelX) (fin : XIR) (s : St) :
    semXIR I (descX6 Lv fin) s = semXIR I fin (lvRun I Lv s 5) := by
  simp only [descX6, semXIR_seq, lvRun]

theorem front6St_size (c : Digest) (π : Proof) (L : Log) : 2 ^ 30 ≤ (front6St c π L).M.size := by
  simp only [front6St, size_sem, initSt, size_runPrims, Array.size_replicate, mem6]
  omega

/-- **The front's and the levels' facts** (EXF: the heap after the front and the fill `fill`; EXG: the concrete
levels and their glue): on an `S` proof of `pz6` bytes whose history has one commitment before the opening at `N₀`,
the state before the descent (after `fill`) has `Inv`, no output, and the descent's machine inputs tied to the
opening's log. -/
def DescIn (Φ : Phases) (fill : XIR) (Lv : ℕ → LevelX) (n₀ b : ℕ) : Prop :=
  ∀ vk c π L x h, (schemeOf (prog6 Φ) P17 vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h) → π.size = pz6 →
    ∀ N₀ (cl : StackClaim6), (Whir.whirP cl).after (h.drop N₀) = some (.ret true) →
      Inv (semXIR (extractorInput c π L).toArray fill (front6St c π L)).M ∧
        (semXIR (extractorInput c π L).toArray fill (front6St c π L)).o = #[] ∧
        Mach (extractorInput c π L).toArray Lv n₀ b (semXIR (extractorInput c π L).toArray fill (front6St c π L))
          (LeanVM.Protocol.Compile.commits h) (h.drop N₀)

/-- **The output map's fact** (EXG's `fin`): from level 0's first `n₀` columns representing a level-0 tuple `U` of
degree `≤ 2^18 + 5`, the stack `decD U` at `colB6`, with `Inv` and no output. -/
def FinOut (fin : XIR) (L0 : LevelX) (n₀ : ℕ) : Prop :=
  ∀ (I : Array Word) (s : St) (U : Whir.Tup E2 (0 + 6)), RepAt s.M L0 (2 ^ 18 - 1 + 6) n₀ U → Inv s.M →
    s.o = #[] → 2 ^ 30 ≤ s.M.size →
    Inv (semXIR I fin s).M ∧ (semXIR I fin s).o = #[] ∧ HeapHolds (semXIR I fin s).M (Whir.decD U)

/-- **`DescProg6` from the descent's round induction** for the descent `fill ; descX6 Lv fin`, given the front's and
the levels' facts and the output map's. -/
theorem descProg6_of {Φ : Phases} {fill : XIR} {Lv : ℕ → LevelX} {fin : XIR} {n₀ b : ℕ}
    (hD : DescIn Φ fill Lv n₀ b) (hF : FinOut fin (Lv 0) n₀) : DescProg6 Φ (.seq fill (descX6 Lv fin)) := by
  intro vk c π L x h hE hl cl hma hgw
  obtain ⟨N₀, -, h1, hs⟩ := hgw openKey_P17
  obtain ⟨hI, hO, hM⟩ := hD vk c π L x h hE hl N₀ cl h1
  obtain ⟨U, hU, hA, hW, hR, hI', hO'⟩ := chainD _ Lv n₀ b _ cl hma _ _ hs hM
  have hsz : 2 ^ 30 ≤ (lvRun (extractorInput c π L).toArray Lv
      (semXIR (extractorInput c π L).toArray fill (front6St c π L)) 5).M.size := by
    simp only [lvRun, size_sem]; exact front6St_size c π L
  obtain ⟨y1, y2, y3⟩ := hF (extractorInput c π L).toArray _ U hR hI' (hO'.trans hO) hsz
  rw [preOut6_eq, semXIR_seq, semXIR_descX6]
  exact ⟨U, ⟨hU, hA, hW⟩, y1, y2, y3⟩

section Assembly

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GWDc Φ.whir) (hF : PhasesFollow Φ P17) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood))

include H HG hF in
/-- **The extractor's fields of `Open6`** at the descent `descX6 Lv fin`, for phases with the deployed opening:
`Len6` discharged (`len6_whirAt`), `DescProg6` from `DescIn` and `FinOut` (`descProg6_of`), the structure and the
size from `DescOk6` and `sizeIR ≤ 2^19`. -/
theorem open6XI (hw : Φ.whir = whirAt Whir.whirP) {fill : XIR} {Lv : ℕ → LevelX} {fin : XIR} {n₀ b : ℕ}
    (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17)) (hD : DescIn Φ fill Lv n₀ b) (hO : FinOut fin (Lv 0) n₀)
    (hok : DescOk6 (.seq fill (descX6 Lv fin))) (hsz : sizeIR (.seq fill (descX6 Lv fin)) ≤ 2 ^ 19) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (.seq fill (descX6 Lv fin))) K) ∧
    (∀ c π L, isS π = false → EX6 (.seq fill (descX6 Lv fin)) c π L = RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (.seq fill (descX6 Lv fin))) (EX6 (.seq fill (descX6 Lv fin))) fuel6 ∧
    (extX6 (.seq fill (descX6 Lv fin))).body.size ≤ progCap :=
  ⟨sound6X H HG hF Xe hX (len6_whirAt hF hw) (descProg6_of hD hO), wBranch6 _, computes6 hok, size_extX6 hsz⟩

end Assembly

end Lvm6.X
