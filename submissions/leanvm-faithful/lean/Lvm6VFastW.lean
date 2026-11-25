-- New for lvm6 (WP-V1, part 2): the twin combinators on top of the frame (`Lvm6VFast`): the decoding of a read in the
-- word field, `twin_map`, and the twins of a read and of `k` draws. (W1's round twins at `chalE2`, written against
-- the earlier opening programs, were removed when W1's deployed opening replaced them; V1b twins `whirP18`.)
import Lvm6VFast

/-!
# Fast twins: combinators

* `decRd π o w`: a read's `E2` value in the word field (16 bytes: two lanes; any other width: the reference
  decoding, never taken on a schedule); `toE2_decRd`.
* `twin_map`, `twin_bind'`, `twin_map'`; `fReadF`; `fSamples`, `twin_samples`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Decoding a read -/

/-- A read's `E2` value in the word field. -/
@[inline] def decRd (π : ByteArray) (o w : Nat) : FE2 :=
  if w = 16 then fe2At π o else FE2.ofE2 (e2OfE (eOfBytes (((bl π).drop o).take w)))

theorem toE2_decRd (π : ByteArray) (o w : Nat) :
    FE2.toE2 (decRd π o w) = e2OfE (eOfBytes (((bl π).drop o).take w)) := by
  unfold decRd
  split
  · subst_vars; exact (e2OfE_read16 π o).symm
  · rfl

/-! ## Combinators -/

theorem twin_map {α β α' β' : Type} {R : ByteArray → β → α → Prop} {R' : ByteArray → β' → α' → Prop}
    {p : VerifierProgram α} {fp : ByteArray → List NV → Option (β × List NV)} (f : α → α') (g : ByteArray → β → β')
    (hp : Twin R p fp) (hg : ∀ π b a, R π b a → R' π (g π b) (f a)) :
    Twin R' (p.bind fun a => .ret (f a)) (fun π tr => (fp π tr).map fun r => (g π r.1, r.2)) := by
  have := twin_bind (R' := R') (f := fun a => VerifierProgram.ret (f a)) (fg := fun b π tr => some (g π b, tr)) hp
    (fun π b a hR tr => Option.Rel.some ⟨hg π b a hR, rfl⟩)
  intro π tr
  have h := this π tr
  dsimp only at h ⊢
  rcases hf : fp π tr with _ | r
  · rw [hf] at h; simpa using h
  · rw [hf] at h; simpa using h

theorem twin_bind' {α β α' β' : Type} {R : ByteArray → β → α → Prop} {R' : ByteArray → β' → α' → Prop}
    {p : VerifierProgram α} {fp : ByteArray → List NV → Option (β × List NV)} {f : α → VerifierProgram α'}
    {fg : β → ByteArray → List NV → Option (β' × List NV)} (hp : Twin R p fp)
    (hf : ∀ π b a, R π b a → ∀ tr, Option.Rel (fun (b : β' × List NV) (a : α' × List Val) =>
      R' π b.1 a.1 ∧ a.2 = b.2.map (NV.val π)) (fg b π tr) (replayP (f a) (tr.map (NV.val π)))) :
    Twin R' (p >>= f) (fun π tr => (fp π tr).bind fun r => fg r.1 π r.2) := twin_bind hp hf

theorem twin_map' {α β α' β' : Type} {R : ByteArray → β → α → Prop} {R' : ByteArray → β' → α' → Prop}
    {p : VerifierProgram α} {fp : ByteArray → List NV → Option (β × List NV)} (f : α → α') (g : ByteArray → β → β')
    (hp : Twin R p fp) (hg : ∀ π b a, R π b a → R' π (g π b) (f a)) :
    Twin R' (p >>= fun a => pure (f a)) (fun π tr => (fp π tr).map fun r => (g π r.1, r.2)) := twin_map f g hp hg

/-- A fast read in the word field. -/
def fReadF (π : ByteArray) (tr : List NV) : Option (FE2 × List NV) :=
  (fRead π tr).map fun r => (decRd π r.1.1 r.1.2, r.2)

/-- Fast `sampleChallenges k`: the next `k` answers. -/
def fSamples : Nat → ByteArray → List NV → Option (List Digest × List NV)
  | 0, _, tr => some ([], tr)
  | k + 1, π, tr => (fSample π tr).bind fun r => (fSamples k π r.2).map fun s => (r.1 :: s.1, s.2)

theorem twin_samples : ∀ k, Twin (fun _ (as : List Digest) cs => as.map chalOf = cs)
    (VerifierProgram.sampleChallenges k) (fSamples k)
  | 0 => twin_ret _ (b := fun _ => []) fun _ => rfl
  | k + 1 => by
    have h := twin_bind' (R' := fun _ (as : List Digest) cs => as.map chalOf = cs)
      (f := fun x => VerifierProgram.sampleChallenges k >>= fun xs => pure (x :: xs))
      (fg := fun a π tr => (fSamples k π tr).map fun s => (a :: s.1, s.2)) twin_sample
      (fun π a c hc tr => by
        simp only [chalR] at hc
        have h2 := twin_map' (R' := fun _ (as : List Digest) cs => as.map chalOf = cs) (fun xs => c :: xs)
          (fun _ s => a :: s) (twin_samples k) (fun π s cs hs => by simp [hs, hc]) π tr
        exact h2)
    intro π tr
    exact h π tr

end Lvm6.V
