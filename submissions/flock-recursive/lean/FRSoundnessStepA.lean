-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2, A.2–A.4; stage S-G1b). The readers follow
-- `submissions/spartan-srom/lean/SpartanSromSoundnessDefs.lean` Part C (`entAt`, `msgOf`, `chAt`),
-- re-stated for Flock's item sequence.
-- RET-1: position-free declarations moved to `FRSoundnessCoreSteps`.
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreTruths`.
import FRSoundnessDefs
import FRProximityFold
import FRSoundnessCoreSteps
import FRSoundnessCoreTruths

/-!
# The transcript read off a chain, and the committed words (BLUEPRINT §5.1, A.2–A.4)

A chain's entries `es` follow the 468 Fiat–Shamir items `fsItems` (`Matches`), so a Fiat–Shamir
position `p` is an index into `es`.

* **Readers** (A.2): the entry at `p` (`entAt`), the absorbed message (`msgAt`: the query from byte
  40, after the tag and the state), its F and K elements (`readF`, `readK`), the challenges of a
  squeeze answer (`fAt es p c`: F coordinate `c ∈ {0, 1}`, bytes `16c … 16c + 15`; `kAt`: the K
  challenge), coordinate `j` of a multi-squeeze phase (`coordAt`), the `k`-th position of a P2
  phase (`posAt`), and the kind from the seed's header (`kindOf`: byte 71 of the seed query, the
  header's first byte).
* **Phase starts** (A.4): `fsStarts` lists the Fiat–Shamir position of each phase's first item
  (`phStart k` for phase `k` of `phases`); `fsStarts_eq` pins it.
* **Committed words** (§5.4): the cap of level `i` (`capPos`, `capDig`: absorbed at position 2 for
  level 0 and at `C.(i−1)` otherwise), the column at position `p` read top-down from its cap entry
  (`colOf`, through `FRMerkle.colL` with the level's encoding `frEnc i`), and the word `wordOf`
  (row `r` at position `p`: the column's F element `r`, `0` where no column is read). `FarAt`: the
  word is not jointly `e`-close to the code `C`, i.e. no agreement set `A` makes it `JointClose`.

Every reader depends on the entries before some position only (`entAt_append`, `Agree`): this is
what each doom predicate's `habs`/`hmid`/`hsingle` use to compare a chain with its extension.
-/

namespace FR.Snd
open RecursionFast FR.Merkle

/-! ## (1) Readers -/

/-! ## Phase starts (A.4) -/

/-! ## (2) The committed words -/

theorem capPos_eq : (List.range 5).map capPos = [2, 330, 369, 396, 420] := by
  unfold capPos phStart; rw [fsStarts_eq]; rfl

/-- **Far**: the word (in K) is not jointly `e`-close to `C`: no agreement set makes it
`JointClose` (BLUEPRINT §5.4). The decoded rows of a close word are `JointClose`'s witness. -/
def FarAt (k : Kind) (C : Submodule K (Fin (2 ^ (lvl k 0).logN) → K)) (e : ℕ) (L es : Log) :
    Prop :=
  ∀ A, ¬ JointClose C e (fun r p => algebraMap F K (wordOf k L es 0 r p)) A

/-! ## Controls -/

/-- Control: on the empty log no column is read, so the word is `0`. -/
theorem wordOf_nil (k : Kind) (es : Log) (i : ℕ) : wordOf k [] es i = 0 := by
  funext r p
  have : colOf k [] es i p = none := by
    unfold colOf
    cases h : (lvl k i).sib <;> simp [colL, pre]
  simp [wordOf, this]

/-- Control: a header with the byte `'P'` gives the kind `P30` (the reader is not constant). -/
theorem kindOf_P30 :
    kindOf [(seedQ 0 0 ⟨(List.replicate 48 (0x50 : UInt8)).toArray⟩, 0)] = .P30 := by
  decide +kernel

/-- Control: a non-kind byte gives the default `L32`. -/
theorem kindOf_default :
    kindOf [(seedQ 0 0 ⟨(List.replicate 48 (0 : UInt8)).toArray⟩, 0)] = .L32 := by
  decide +kernel

end FR.Snd
