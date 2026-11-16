-- Ported from leanVM `formal/Statement/Keccak.lean` (formal rev 40f877dc) as `LvmKeccakSpec` for lvm (WP-2).

import Mathlib.Data.Nat.Notation

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmM3MidOff`, outside its import closure.)

/-!
# Keccak

Keccak-f[1600] as leanVM computes it, and Keccak-256 over any permutation of its state, in any
monad (`keccak256With`), the deployed one over Keccak-f[1600] (`keccak256`). Every party hashes with
Keccak-256 over the permutation it is given, `π` in the model (`RandomPermutation.lean`). The
permutation's state is one type throughout, `KeccakState`: `25` lanes of `64` bits, lane `x + 5y`
at index `x + 5y`.

The source is `crates/verifier/src/hash.rs` at leanVM `40f877dc2c858f013c5974ab71ca594b31a7aec9`
(also `crates/primitives/src/hash.rs`): the round constants, rotation offsets and lane permutation
(`KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`, `hash.rs:11-49`), the permutation `keccak_f`
(`hash.rs:50-69`) and the hash `keccak_hash` (`hash.rs:77-97`, its rate `:8`): Keccak-256 as
Ethereum computes it, rate `136` bytes, the message padded with `0x01 ‖ 0^* ‖ 0x80` (FIPS 202's
SHA3-256 would put `0x06` first).
-/

section

namespace LeanVM.Parameters

/-- `KECCAK_RC` (`hash.rs:11-36`): the round constants of the `24` rounds. -/
def keccakRC : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `KECCAK_RHO` (`hash.rs:37-39`): the rotation of each lane, by index `x + 5y`. -/
def keccakRho : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `KECCAK_PI` (`hash.rs:40-49`): where lane `i = x + 5y` lands,
`⌊i/5⌋ + 5 · ((2 · (i % 5) + 3 · ⌊i/5⌋) % 5)`. -/
def keccakPi (i : ℕ) : ℕ := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

/-! ### Keccak-f[1600] -/

/-- A Keccak state: `25` lanes of `64` bits, lane `x + 5y` at index `x + 5y`. -/
abbrev KeccakState := Vector UInt64 25

namespace Keccak

/-- Lane `i` of a state, `0` past the end. -/
def lane (a : KeccakState) (i : ℕ) : UInt64 := a.toArray.getD i 0

/-- Rotate a lane left by `n < 64` bits (`u64::rotate_left`). -/
def rot (x : UInt64) (n : ℕ) : UInt64 :=
  if n = 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One round of `keccak_f` with the round constant `rc` (`hash.rs:52-67`): θ, then ρ and π
(`b[KECCAK_PI[i]] = a[i].rotate_left(KECCAK_RHO[i])`), then χ and ι. -/
def round (a : KeccakState) (rc : UInt64) : KeccakState :=
  let c : Vector UInt64 5 := Vector.ofFn fun x ↦
    lane a x ^^^ lane a (x + 5) ^^^ lane a (x + 10) ^^^ lane a (x + 15) ^^^ lane a (x + 20)
  let cAt := fun x ↦ c.toArray.getD x 0
  -- θ: `a[i] ^ c[(i + 4) % 5] ^ c[(i + 1) % 5].rotate_left(1)`
  let a : KeccakState := Vector.ofFn fun i ↦
    lane a i ^^^ cAt ((i.val + 4) % 5) ^^^ rot (cAt ((i.val + 1) % 5)) 1
  -- ρ and π
  let b : KeccakState := (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (rot (lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)
  -- χ
  let a : KeccakState := Vector.ofFn fun i ↦
    lane b i ^^^ (~~~ lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
      lane b (i.val - i.val % 5 + (i.val + 2) % 5))
  -- ι
  a.setIfInBounds 0 (lane a 0 ^^^ rc)

end Keccak

/-- **Keccak-f[1600]** (`keccak_f`, `hash.rs:50-69`): the `24` rounds. -/
def keccakF1600 (a : KeccakState) : KeccakState := keccakRC.foldl Keccak.round a

end LeanVM.Semantics

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

/-- A Keccak-256 digest: its `32` bytes as four little-endian 64-bit words, the first four lanes of
the last state (`Digest::words`, `hash.rs:105-107`). -/
abbrev Digest := Vector UInt64 4

namespace KeccakHash

/-! ### Keccak-256 (its constants and `keccak_hash`, `hash.rs:8`, `:77-97`) -/

/-- `RATE`: a block is `136` bytes, `17` lanes. -/
def rate : ℕ := 136

section With

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

end With

/-! ### Bytes of words and digests -/

/-- The eight little-endian bytes of a 64-bit word. -/
def wordBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun k ↦ (w >>> (8 * k).toUInt64).toUInt8

/-- The 32 bytes of a digest: its words, little-endian (`hash.rs:92-96`). -/
def digestBytes (digest : Digest) : List UInt8 := digest.toList.flatMap wordBytes

end KeccakHash

end LeanVM.Protocol
