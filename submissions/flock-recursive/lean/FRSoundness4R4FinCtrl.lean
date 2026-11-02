-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c): controls.
import FRSoundness4R4FinSh
import FRSoundness4R4Kind

/-!
# Controls for R4c's definitions

* (+) **At 3.x's parameters the relocated relations are 3.x's** (`relZ4_fin3P`, `relLr4_fin3P`,
  `relB4_fin3P`, `relLc4_fin3P`): the generalisation changes nothing at `fin3P`.
* (−) **The flags reject** a wrong claim register (`relZ4_rejects`, `relLr4_rejects`), and a node's
  `relLr4` is not vacuous (`relLr4_leaf`: only a leaf's is `true` outright).
* (+/−) `OutsLt` holds on the empty context, and fails on a context exporting `next` itself.
* (+) `kindOfC`'s byte: `byteAt_bytesOf_cons`; (−) the seed's constant is not a kind byte at `0`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

theorem pe4_seq3 (inp : Input) {f : ℕ} (hf : f < 19) (o : ℕ) : pe4 seq3 inp f o = pe inp f o := by
  rw [pe4, pe, ← absOff_seq3 hf, absOff_zero]

section Ctrl
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- (+) `relZ4` at `fin3P` is 3.x's `relZ`. -/
theorem relZ4_fin3P : relZ4 κ inp fi r fin3P = relZ κ inp fi r := by
  simp only [relZ4, relZ, show fin3P.S = seq3 from rfl, pe4_seq3 inp (show fZend < 19 by decide)]
  rw [seq3_eq]; rfl

/-- (+) `relLr4` at `fin3P` is 3.x's `relLr`. -/
theorem relLr4_fin3P : relLr4 κ inp fi r fin3P = relLr κ inp fi r := by
  simp only [relLr4, relLr, show fin3P.S = seq3 from rfl, pe4_seq3 inp (show fLrEnd < 19 by decide)]
  rfl

/-- (+) `relB4` at `fin3P` is 3.x's `relB`. -/
theorem relB4_fin3P : relB4 κ inp fi r fin3P = relB κ inp fi r := by
  have h : ∀ o, fieldOffOf seq3 fStmt + o = absOff fStmt o := fun o => by
    rw [← absOff_seq3 (show fStmt < 19 by decide), absOff_zero]
  simp only [relB4, relB, vStar4, vStar, pubH4, pubH, show fin3P.S = seq3 from rfl, h]
  rfl

/-- (+) `relLc4` at `fin3P` is 3.x's `relLc`. -/
theorem relLc4_fin3P : relLc4 impl κ inp fi r fin3P = relLc impl κ inp fi r := by
  have h3 : phaseOffOf seq3 (phaseIx "L3") fL2 = phaseOff (phaseIx "L3") fL2 := phaseOffOf_seq3 _ _
  simp only [relLc4, relLc, lcWalk4, lcWalk, lcFree4, lcFree, lcVf4, lcVf, lcV4, lcV, lcRhi4, lcRhi,
    show fin3P.S = seq3 from rfl, h3, pe4_seq3 inp (show fZend < 19 by decide),
    pe4_seq3 inp (show fL2 < 19 by decide)]
  rw [seq3_eq]; rfl

/-- (−) **`relZ4` rejects a wrong `c_Z`**: if Z3's last claim register holds a value other than
`eq·â·b̂`, the flag is `false`. -/
theorem relZ4_rejects (P : FinP) {v : F}
    (hv : rd r (claimN fi "Z3") = .f v)
    (hne : v ≠ eqPoint (List.ofFn pinnedRho ++ ((coordsR fi "Z1").take (P.kv.m κ - 13)).map (fv r)).toArray
      (((chals fi "Z3" P.S.z3).take (P.kv.m κ - 6)).map (fv r)).toArray *
        pe4 P.S inp fZend 0 * pe4 P.S inp fZend 16) :
    relZ4 κ inp fi r P = false := by
  simp only [relZ4, hv, Val.eqv, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact .inl (fun h => hne h.symm)

/-- (−) **`relLr4` rejects a node's wrong end claim.** -/
theorem relLr4_rejects (P : FinP) (hn : P.kv.node κ = true) {v : F}
    (hv : rd r (claimN fi "Lr2") = .f v)
    (hne : v ≠ eqPoint (((coordsR fi "Lr1").take P.lrR).map (fv r)).toArray
      ((chals fi "Lr2" P.lrR).map (fv r)).toArray *
        (pe4 P.S inp fLrEnd 0 * pe4 P.S inp fLrEnd 16 + pe4 P.S inp fLrEnd 32)) :
    relLr4 κ inp fi r P = false := by
  simp only [relLr4, hn, ite_true, hv, Val.eqv, decide_eq_false_iff_not]
  exact fun h => hne h.symm

/-- (+) A leaf's `relLr4` is `true` (the end check is a node's). -/
theorem relLr4_leaf (P : FinP) (hn : P.kv.node κ = false) : relLr4 κ inp fi r P = true := by
  simp [relLr4, hn]

end Ctrl

/-- (+) The empty context's outs are below its `next`. -/
theorem outsLt_ctx0 : OutsLt ctx0 := fun m x hx => by
  simp [ctx0, Array.getD_eq_getD_getElem?] at hx

/-- (−) A context exporting its own `next` fails `OutsLt`. -/
theorem not_outsLt_self : ¬ OutsLt ⟨0, 0, 0, [], [], 0, #[[0]]⟩ := fun h => by
  have := h 0 0 (by simp [Array.getD_eq_getD_getElem?]); simp at this

/-- (−) The seed's constant `[p.byte, …]` is not a kind byte for the zero byte (so `kindOfC_byte4`
needs `p.byte ≠ 0`). -/
theorem kind_zero_none : CKind.ofByte? 0 = none := by decide

end FR.Snd.R4
