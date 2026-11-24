-- lvm6 X2 (part 2): the chain scan against the compiled scheme (FORMAT6 v2.5: seed `a₀ ‖ HDR`). New.
import Lvm6XChain

/-!
# The scan's chain is the scheme's

* **`fmAns6_zero`**, **`fmAns6_one`**: positions 0 and 1 of the first-match chain are the answers the
  specification extractor (`Lvm.FS.Scheme.Ex`) finds for `q₀` and for the seed `seedQ a₀ x`, `x` the header
  bytes (v2.5: `enc6 x = x`, so the seed is `fsQ6 1 a₀ = a₀ ‖ π[0, hdrLen)`, `fsQ6_one`).
* **`Chain6Spec`** (frozen; `chain6_spec` proves it): on an accepting replay `trun` from the seed's answer, the
  `j`-th challenge of the history is `chalOf` of position `j + 2` of the first-match chain.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X
open LeanVM.Protocol.Compile (Ev)

/-- The challenges of a history, in order. -/
def samples (H : List Ev) : List LeanVM.Parameters.E :=
  H.filterMap fun
    | .sample c => some c
    | _ => none

/-- **`chain6_spec`'s statement**: the challenges of an accepting replay are the first-match chain's. -/
def Chain6Spec (sh : Shape) : Prop :=
  ∀ (vk : Digest) (dec : List UInt8 → List V.Val → Bool) (π : Proof) (L : Log) (x body : List UInt8)
    (a₁ : Digest) (H : List Ev),
    (V.scheme6V (toV sh) vk dec).hdr π = some (x, body) →
    fmAns (fsQ6 sh π) zeroDL L 1 = some a₁ →
    (V.scheme6V (toV sh) vk dec).trun L ((V.scheme6V (toV sh) vk dec).P x) a₁ [] [] body [] = some (true, H) →
    ∀ j (hj : j < (samples H).length), j + 2 < nCh6 sh →
      ∃ a, fmAns (fsQ6 sh π) zeroDL L (j + 2) = some a ∧ (samples H)[j] = Lvm.FS.chalOf a

/-- Position 0 is `q₀`'s first answer. -/
theorem fmAns6_zero (sh : Shape) (π : Proof) (L : Log) :
    fmAns (fsQ6 sh π) zeroDL L 0 = (L.find? fun e => e.1 = Lvm.FS.toQ V.q06).map Prod.snd := by
  simp only [fmAns, fsQ6, if_pos]

/-- **The seed query** (v2.5): the previous answer, then the header `π[0, hdrLen)`. -/
theorem fsQ6_one (sh : Shape) (π : Proof) (a : Digest) :
    fsQ6 sh π 1 a = Lvm.FS.toQ (a.toList ++ π.data.toList.take (hdrLen sh)) := by
  have hm : msg6 sh 1 = (0, hdrLen sh) := rfl
  rw [fsQ6, if_neg (by decide), hm]
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_extract, Lvm.FS.toQ, digestBytes]
  apply Array.ext'
  simp [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  rfl

/-- **Position 1 is the seed's first answer**, the seed query being the scheme's `seedQ a₀ x` on the header
bytes `x`. -/
theorem fmAns6_one (sh : Shape) (vk : Digest) (dec : List UInt8 → List V.Val → Bool) (π : Proof) (L : Log) :
    fmAns (fsQ6 sh π) zeroDL L 1 = (fmAns (fsQ6 sh π) zeroDL L 0).bind fun a₀ =>
      (L.find? fun e => e.1 = (V.scheme6V (toV sh) vk dec).seedQ a₀ (π.data.toList.take (hdrLen sh))).map
        Prod.snd := by
  show ((fmAns (fsQ6 sh π) zeroDL L 0).bind fun st => (L.find? fun e => e.1 = fsQ6 sh π 1 st).map Prod.snd) = _
  congr 1
  funext a₀
  rw [fsQ6_one]
  rfl

end Lvm6.X
