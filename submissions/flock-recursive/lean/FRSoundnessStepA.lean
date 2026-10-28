-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2, A.2–A.4; stage S-G1b). The readers follow
-- `submissions/spartan-srom/lean/SpartanSromSoundnessDefs.lean` Part C (`entAt`, `msgOf`, `chAt`),
-- re-stated for Flock's item sequence.
-- RET-1: position-free declarations moved to `FRSoundnessCoreSteps`.
import FRSoundnessDefs
import FRProximityFold
import FRSoundnessCoreSteps

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

/-- **The kind of a chain**: the header's first byte (byte 71 of the seed query
`"FRSEED0" ‖ vk ‖ c ‖ hdr`); `L32` if it is not a kind byte. -/
def kindOf (es : Log) : Kind := (((entAt es 0).1.data[71]?).bind Kind.ofByte?).getD .L32

theorem kindOf_congr {es es' : Log} (h : Agree es es' 1) : kindOf es = kindOf es' := by
  simp only [kindOf, h 0 one_pos]

/-! ## Phase starts (A.4) -/

/-- The Fiat–Shamir position of each phase's first item, in the order of `phases` (a phase with
no Fiat–Shamir item, `Q`, gets the position of the next one). -/
def fsStarts : List ℕ :=
  (phases.foldl (fun (acc : ℕ × List ℕ) p =>
    (acc.1 + (p.shape.items.filter Item.isFS).length, acc.2 ++ [acc.1])) (0, [])).2

/-- The first Fiat–Shamir position of phase `k` of `phases`. -/
def phStart (k : ℕ) : ℕ := fsStarts.getD k 0

/-- Control: the phase starts (A.4; `piopPhases` are phases `0 … 25` (revision 3.12: E4 at 24), level `i`'s
`P1, C, P2, Q, P3` are `26 + 5i … 30 + 5i`, `Pf` is `51`). -/
theorem fsStarts_eq : fsStarts = [0, 1, 2, 3, 13, 15, 67, 68, 69, 97, 98, 99, 114, 170, 178, 208,
    209, 210, 221, 263, 264, 265, 311, 312, 313, 317, 318, 330, 331, 356, 356, 361, 369, 370, 383,
    383, 388, 396, 397, 407, 407, 412, 420, 421, 429, 429, 434, 442, 443, 449, 449, 454] := by
  decide +kernel

/-! ## (2) The committed words -/

/-- The position of level `i`'s cap absorb: `cap₀` (phase 2), else `C.(i − 1)` (phase `22 + 5i`). -/
def capPos (i : ℕ) : ℕ := if i = 0 then phStart 2 else phStart (22 + 5 * i)

theorem capPos_eq : (List.range 5).map capPos = [2, 330, 369, 396, 420] := by
  unfold capPos phStart; rw [fsStarts_eq]; rfl

/-- Cap entry `c` of level `i`: the 32 bytes at offset `32c` of the cap's message (A.2). -/
def capDig (es : Log) (i c : ℕ) : Digest := bytesAt (msgAt es (capPos i)) (32 * c) 32

/-- **The column of level `i` at position `p`** for kind `k`, read off `L` top-down from its cap
entry (`p / 2^sib`) along the bits of `p` (`colL (frEnc i)`, height `sib = log₂ n − cap`). -/
def colOf (k : Kind) (L es : Log) (i p : ℕ) : Option ByteArray :=
  colL (frEnc i) L (capDig es i (p / 2 ^ (lvl k i).sib)) (lvl k i).sib p

/-- **The committed word of level `i`**: row `r` at position `p` is the column's F element `r`
(16 bytes each, row 0 first, A.2); `0` where `L` reads no column. -/
def wordOf (k : Kind) (L es : Log) (i : ℕ) : Fin (lvl k i).rows → Fin (2 ^ (lvl k i).logN) → F :=
  fun r p => ((colOf k L es i p).map fun col => readF col (16 * r)).getD 0

/-- **Far**: the word (in K) is not jointly `e`-close to `C`: no agreement set makes it
`JointClose` (BLUEPRINT §5.4). The decoded rows of a close word are `JointClose`'s witness. -/
def FarAt (k : Kind) (C : Submodule K (Fin (2 ^ (lvl k 0).logN) → K)) (e : ℕ) (L es : Log) :
    Prop :=
  ∀ A, ¬ JointClose C e (fun r p => algebraMap F K (wordOf k L es 0 r p)) A

/-- The column depends on the entries up to the cap's absorb only. -/
theorem colOf_congr (k : Kind) (L : Log) {es es' : Log} (i p : ℕ)
    (h : Agree es es' (capPos i + 1)) : colOf k L es i p = colOf k L es' i p := by
  simp only [colOf, capDig, msgAt, h (capPos i) (by omega)]

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
