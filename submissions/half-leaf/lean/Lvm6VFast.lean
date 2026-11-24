-- New for lvm6 (WP-V1, part 2): the frame of the per-phase fast twins. A phase program is replayed on a slice
-- of the walk's transcript (`replayP`); a fast twin reads the driver's transcript (offsets and answers into `π`)
-- with word-field arithmetic (`FE2`), and is proved to agree with `replayP` up to a value relation (`Twin`).
-- Twins compose along `bind`, so the decision `F` is the composition of the phase twins.
import Lvm6VReplay
import LvmVEqCodec
import LvmFieldE2Correct
import LvmE2Grind

/-!
# Fast twins of phase programs

* **`replayP p tr`**: the phase program `p` replayed on the transcript `tr` (oldest first): its value and the
  rest of the transcript. `replay_eq`: the decision's `replay` is `replayP` used up exactly with `true`;
  `replayP_bind`: replaying `p >>= f` is replaying `p`, then `f` on the rest.
* **`Twin R p fp`**: on every proof `π` and driver transcript `tr`, `fp π tr` and `replayP p (tr.map (NV.val π))`
  are both `none`, or both `some` with values related by `R` and the same rest. Rules: `twin_ret`, `twin_bind`
  (composition), `twin_read` (a read: its offset and width), `twin_sample` (a draw: its answer).
* **Decoding**: a 16-byte read at `o` is `toE2 (fe2At π o)` after `e2OfE` (`e2OfE_read16`); a draw's challenge
  is `toE2 (fe2OfAns a)` (`e2OfE_chal`); the proof of work of a draw is `pw` on `answerBits` (`powOK_chal`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Replaying a phase on a slice of the transcript -/

/-- **A phase program replayed on a transcript** (oldest first): its value and the rest. -/
def replayP {α : Type} : VerifierProgram α → List Val → Option (α × List Val)
  | .ret a, tr => some (a, tr)
  | .read k, .e x :: tr => replayP (k x) tr
  | .sample k, .c c :: tr => replayP (k c) tr
  | .commit ht w k, .cap ht' w' :: tr => if ht = ht' ∧ w = w' then replayP k tr else none
  | .query i ps k, .rows i' ps' r :: tr => if i = i' ∧ ps = ps' then replayP (k r) tr else none
  | _, _ => none

/-- The decision's `replay` is `replayP` ending with `true` and the transcript used up. -/
theorem replay_eq (p : VerifierProgram Bool) : ∀ tr, replay p tr = match replayP p tr with
    | some (b, []) => b
    | _ => false := by
  induction p with
  | ret b => intro tr; cases tr <;> rfl
  | fail => intro tr; cases tr <;> rfl
  | grind _ _ _ => intro tr; cases tr <;> rfl
  | read k ih =>
    intro tr
    rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v <;> first | rfl | exact ih _ _
  | sample k ih =>
    intro tr
    rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v <;> first | rfl | exact ih _ _
  | commit ht w k ih =>
    intro tr; rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v with
      | cap ht' w' =>
        simp only [replay, replayP]
        by_cases h : ht = ht' ∧ w = w'
        · obtain ⟨rfl, rfl⟩ := h; simp [ih]
        · rw [if_neg h]
          have : (ht == ht' && w == w') = false := by
            simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
          rw [this, Bool.false_and]
      | _ => rfl
  | query i ps k ih =>
    intro tr; rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v with
      | rows i' ps' r =>
        simp only [replay, replayP]
        by_cases h : i = i' ∧ ps = ps'
        · obtain ⟨rfl, rfl⟩ := h; simp [ih]
        · rw [if_neg h]
          have : (i == i' && ps == ps') = false := by
            simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
          rw [this, Bool.false_and]
      | _ => rfl

/-- **Replaying a composition** is replaying the first phase, then the second on the rest. -/
theorem replayP_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) :
    ∀ tr, replayP (p.bind f) tr = (replayP p tr).bind fun r => replayP (f r.1) r.2 := by
  induction p with
  | ret a => intro tr; rfl
  | fail => intro tr; cases tr <;> rfl
  | grind _ _ _ => intro tr; cases tr <;> rfl
  | read k ih =>
    intro tr
    rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v <;> first | rfl | exact ih _ _
  | sample k ih =>
    intro tr
    rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v <;> first | rfl | exact ih _ _
  | commit ht w k ih =>
    intro tr; rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v with
      | cap ht' w' =>
        simp only [VerifierProgram.bind, replayP]
        split
        · exact ih _
        · rfl
      | _ => rfl
  | query i ps k ih =>
    intro tr; rcases tr with _ | ⟨v, tr⟩
    · rfl
    · cases v with
      | rows i' ps' r =>
        simp only [VerifierProgram.bind, replayP]
        split
        · exact ih _ _
        · rfl
      | _ => rfl

/-! ## Twins -/

/-- **`fp` is a fast twin of the phase `p`** up to the value relation `R` (which may read `π`). -/
def Twin {α β : Type} (R : ByteArray → β → α → Prop) (p : VerifierProgram α)
    (fp : ByteArray → List NV → Option (β × List NV)) : Prop :=
  ∀ π tr, Option.Rel (fun (b : β × List NV) (a : α × List Val) => R π b.1 a.1 ∧ a.2 = b.2.map (NV.val π))
    (fp π tr) (replayP p (tr.map (NV.val π)))

theorem twin_ret {α β : Type} (R : ByteArray → β → α → Prop) {a : α} {b : ByteArray → β} (h : ∀ π, R π (b π) a) :
    Twin R (.ret a) (fun π tr => some (b π, tr)) := fun π _ => Option.Rel.some ⟨h π, rfl⟩

theorem twin_bind {α β α' β' : Type} {R : ByteArray → β → α → Prop} {R' : ByteArray → β' → α' → Prop}
    {p : VerifierProgram α} {fp : ByteArray → List NV → Option (β × List NV)} {f : α → VerifierProgram α'}
    {fg : β → ByteArray → List NV → Option (β' × List NV)} (hp : Twin R p fp)
    (hf : ∀ π b a, R π b a → ∀ tr, Option.Rel (fun (b : β' × List NV) (a : α' × List Val) =>
      R' π b.1 a.1 ∧ a.2 = b.2.map (NV.val π)) (fg b π tr) (replayP (f a) (tr.map (NV.val π)))) :
    Twin R' (p.bind f) (fun π tr => (fp π tr).bind fun r => fg r.1 π r.2) := by
  intro π tr
  dsimp only
  rw [replayP_bind]
  have h := hp π tr
  rcases hf1 : fp π tr with _ | b <;> rcases hr1 : replayP p (tr.map (NV.val π)) with _ | a <;>
    rw [hf1, hr1] at h
  · exact Option.Rel.none
  · cases h
  · cases h
  · cases h with
    | some h =>
      obtain ⟨hR, hrest⟩ := h
      simp only [Option.bind_some]
      rw [hrest]
      exact hf π b.1 a.1 hR b.2

/-- **A read**: its offset and width. -/
def fRead : ByteArray → List NV → Option ((Nat × Nat) × List NV)
  | _, .rd o w :: tr => some ((o, w), tr)
  | _, _ => none

/-- A read's value is `eOfBytes` of its bytes. -/
def readR (π : ByteArray) (ow : Nat × Nat) (x : E) : Prop := eOfBytes (((bl π).drop ow.1).take ow.2) = x

theorem twin_read : Twin readR VerifierProgram.readScalar fRead := by
  intro π tr
  rcases tr with _ | ⟨v, tr⟩
  · exact Option.Rel.none
  · cases v with
    | rd o w => exact Option.Rel.some ⟨rfl, rfl⟩
    | _ => exact Option.Rel.none

/-- **A draw**: its answer. -/
def fSample : ByteArray → List NV → Option (Digest × List NV)
  | _, .draw a :: tr => some (a, tr)
  | _, _ => none

/-- A draw's value is `chalOf` of its answer. -/
def chalR (_ : ByteArray) (a : Digest) (c : E) : Prop := chalOf a = c

theorem twin_sample : Twin chalR VerifierProgram.sampleChallenge fSample := by
  intro π tr
  rcases tr with _ | ⟨v, tr⟩
  · exact Option.Rel.none
  · cases v with
    | draw a => exact Option.Rel.some ⟨rfl, rfl⟩
    | _ => exact Option.Rel.none

/-! ## Decoding into the word field -/

theorem limb_eOfBytes (l : List UInt8) (j : Fin 3) : (eOfBytes l).limb j = kOfBytes (l.drop (8 * j.val)) :=
  congrFun (Equiv.apply_symm_apply (CompPoly.Extension.Ext.equivFn BF64.ext3Params)
    (fun j : Fin BF64.ext3Params.d => kOfBytes (l.drop (8 * j.val)))) j

/-- The `E2` value of 16 bytes at `o`. -/
@[inline] def fe2At (π : ByteArray) (o : Nat) : FE2 := ⟨Lvm.kAt π o, Lvm.kAt π (o + 8)⟩

/-- The challenge of an answer in the word field. -/
@[inline] def fe2OfAns (a : Digest) : FE2 := fe2At (Lvm.digestBytes a) 0

theorem e2OfE_read16 (π : ByteArray) (o : Nat) :
    e2OfE (eOfBytes (((bl π).drop o).take 16)) = FE2.toE2 (fe2At π o) := by
  simp only [e2OfE, limb_eOfBytes, FE2.toE2, fe2At]
  congr 1
  · refine (Lvm.VEq.toBF64_kAt_of π o _ fun i hi => ?_).symm
    rw [show 8 * (0 : Fin 3).val = 0 from rfl, List.drop_zero, get!_bl, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  · refine (Lvm.VEq.toBF64_kAt_of π (o + 8) _ fun i hi => ?_).symm
    rw [show 8 * (1 : Fin 3).val = 8 from rfl, get!_bl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_drop, List.getElem?_take, if_pos (by omega), List.getElem?_drop, Nat.add_assoc]

theorem e2OfE_chal (a : Digest) : e2OfE (chalOf a) = FE2.toE2 (fe2OfAns a) := by
  simp only [e2OfE, chalOf, limb_eOfBytes, FE2.toE2, fe2OfAns, fe2At]
  congr 1
  · refine (Lvm.VEq.toBF64_kAt_of _ 0 _ fun i hi => ?_).symm
    rw [Lvm.VEq.get!_digestBytes, Nat.zero_add]; rfl
  · refine (Lvm.VEq.toBF64_kAt_of _ 8 _ fun i hi => ?_).symm
    rw [Lvm.VEq.get!_digestBytes, show 8 * (1 : Fin 3).val = 8 from rfl, Lvm.VEq.getD_drop_bytes]

end Lvm6.V
