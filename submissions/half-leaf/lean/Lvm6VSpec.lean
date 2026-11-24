-- New for lvm6 (WP-V1, part 1): the specified verifier of FORMAT6 §1–§6 as a compiled scheme
-- (`Lvm.FS.Scheme`, season 1's FS compiler): the header and statement check, the seed, and the
-- program that walks the schedule (reads, draws with their proof of work and positions, caps,
-- openings) and hands its transcript to a decision.
import Lvm6VSched
import LvmCompileCodec
import LvmVCore
import LvmDriver

/-!
# The specified `V_S`: FORMAT6 as a compiled scheme

**The walk** (`Prims.walk`). The schedule is read through seven primitives (`Prims`): `skip`, `seq`,
`rd w` (one read of `w` bytes, absorbed), `draw chk upd` (one draw; reject unless `chk N`, then update the
positions with `upd ps N`, where `N` is the 192-bit number of the answer's lanes 0–2), `cap ht w`
(a cap, absorbed), `reset` (forget the positions) and `opn i` (open commitment `i` at the positions).
`Prims.item` expands one `Item`: `E k` is `k` reads of 16 bytes, `K k` is `k` reads of 8, `G g` is an 8-byte
read (the nonce)
and a draw with `pw g` (`N < 2^(192−g)`: lane 2 `< 2^(64−g)`, FORMAT6 §4), `D k` is `k` plain draws, `B` one plain draw (its value goes to the transcript; no decision reads it),
`pos i g` is a reset, the nonce and `draws` draws whose `N mod 2^128` gives `⌊128/ht⌋` positions each
(`posList`, FORMAT6 §5), the first with `pw g`. The same expansion serves the specification (`PS`,
programs of the verifier language) and the executable driver (`Lvm6VDrive`), so they agree by
construction on the order of items.

**The specification** `PS`: a read is `read` (the scheme's width of the `n`-th read is `rwOf sched n`, as
season 1's `rw`: an `E` scalar is one 16-byte read, `decE` puts `c₀, c₁` in limbs 0–1, the phase programs'
`e2Read`), a draw is `sample` (the compiled verifier asks `st ‖ buf`), a cap is `commit`, an opening is
`query`. The transcript (`Val`: reads, challenges, cap shapes, openings with their index and positions,
newest first) goes to a decision `dec x tr` at the end, `x` the header bytes.

**The scheme** `scheme6V sh vk dec`: the statement is the header `HDR` (`hdrLen = 136 + 16 v` bytes,
FORMAT6 v2.2 §2); `ok c x` checks the magic, `b ∈ {0, 1}`, `n = N★`, `b = 0 ⟹ c' = 0`, `HDR.vk = vk` and the
statement (`c = leafStmt h n` or `nodeStmt c' (leafStmt h n)`); the seed is `a₀ ‖ HDR` (v2.5, `enc = id`); `q₀ =
"lvm6/1\0"`; caps and occupied words by height and width (`capOfL`, `occL`); read widths `rwOf sched`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Draws: proof of work and positions -/

/-- The proof of work of `g` bits on the 192-bit number `N` of an answer's lanes 0–2: lane 2 has its top
`g` bits zero. -/
def pw (g N : Nat) : Bool := decide (N < 2 ^ (192 - g))

/-- `cnt` positions of `ht` bits from `N`, low bits first (FORMAT6 §5). -/
def posList (ht cnt N : Nat) : List Nat := (List.range cnt).map fun j => (N >>> (j * ht)) % 2 ^ ht

/-- Accept every answer. -/
def tt : Nat → Bool := fun _ => true

/-- Keep the positions. -/
def keepPs : List Nat → Nat → List Nat := fun ps _ => ps

/-- Append `cnt` positions of `ht` bits from lanes 0–1 of the answer. -/
def addPs (ht cnt : Nat) : List Nat → Nat → List Nat := fun ps N => ps ++ posList ht cnt (N % 2 ^ 128)

/-! ## The schedule through seven primitives -/

/-- The primitives a schedule is read through. -/
structure Prims (σ : Type) where
  skip : σ
  seq : σ → σ → σ
  rd : Nat → σ
  draw : (Nat → Bool) → (List Nat → Nat → List Nat) → σ
  cap : Nat → Nat → σ
  reset : σ
  opn : Nat → σ

namespace Prims

variable {σ : Type} (P : Prims σ) (L : List Lev)

/-- `m` times `f`. -/
def rep (f : σ) : Nat → σ
  | 0 => P.skip
  | m + 1 => P.seq f (rep f m)

/-- The further draws of a level's positions. -/
def posRest (ht : Nat) : List Nat → σ
  | [] => P.skip
  | c :: cs => P.seq (P.draw tt (addPs ht c)) (posRest ht cs)

/-- **One item.** -/
def item : Item → σ
  | .E k => P.rep (P.rd 16) k
  | .K k => P.rep (P.rd 8) k
  | .cap i => P.cap (L.getD i default).ht (L.getD i default).wd
  | .G g => P.seq (P.rd 8) (P.draw (pw g) keepPs)
  | .D k => P.rep (P.draw tt keepPs) k
  | .B => P.draw tt keepPs
  | .pos i g =>
    P.seq P.reset (P.seq (P.rd 8) (P.seq (P.draw (pw g) (addPs (L.getD i default).ht ((L.getD i default).cnts.headD 0)))
      (P.posRest (L.getD i default).ht (L.getD i default).cnts.tail)))
  | .open i => P.opn i

/-- **A schedule.** -/
def walk : List Item → σ
  | [] => P.skip
  | it :: r => P.seq (P.item L it) (walk r)

end Prims

/-! ## The specification: programs of the verifier language -/

/-- A value of the transcript. -/
inductive Val
  /-- One read (`decE` of its bytes: limbs 0–1 of a 16-byte scalar, limb 0 of an 8-byte word). -/
  | e (x : E)
  /-- One draw (`chalOf`: lanes 0–2 of the answer). -/
  | c (x : E)
  /-- A cap read for a commitment of `2^ht` rows of `w` words. -/
  | cap (ht w : Nat)
  /-- The rows of one opening of commitment `i` at the positions `ps`, in their order. -/
  | rows (i : Nat) (ps : List Nat) (r : List (List K))

/-- A continuation: positions and transcript (newest first) to a program. -/
abbrev Kt : Type := List Nat → List Val → VerifierProgram Bool

/-- A step of the specification. -/
abbrev St : Type := List Nat → List Val → Kt → VerifierProgram Bool

/-- **The specification's primitives.** -/
def PS : Prims St where
  skip := fun ps acc k => k ps acc
  seq := fun f g ps acc k => f ps acc fun ps' acc' => g ps' acc' k
  rd := fun _ ps acc k => .read fun x => k ps (.e x :: acc)
  draw := fun chk upd ps acc k => .sample fun c =>
    if chk (LeanVM.Protocol.Verifier.eToNat c) then k (upd ps (LeanVM.Protocol.Verifier.eToNat c)) (.c c :: acc)
    else .fail
  cap := fun ht w ps acc k => .commit ht w (k ps (.cap ht w :: acc))
  reset := fun _ acc k => k [] acc
  opn := fun i ps acc k => .query i ps fun rows => k ps (.rows i ps rows :: acc)

/-! ## The header (FORMAT6 §2) -/

/-- The shape `V_S` is generic in. -/
structure VShape where
  /-- The one leaf size `V_S` accepts. -/
  nStar : Nat
  /-- `v`: the accumulator point's coordinates. -/
  phiVars : Nat
  /-- The opened levels. -/
  levs : List Lev
  /-- The schedule of `BODY`. -/
  sched : List Item

/-- Bytes of the header (v2.2: `vk` at byte 88). -/
def hdrLen (sh : VShape) : Nat := 136 + 16 * sh.phiVars

/-- The magic `"Slvm6"`, 0, 0, version 1. -/
def magic6 : List UInt8 := [0x53, 0x6C, 0x76, 0x6D, 0x36, 0x00, 0x00, 0x01]

/-- The first query `"lvm6/1"`, 0. -/
def q06 : List UInt8 := [0x6C, 0x76, 0x6D, 0x36, 0x2F, 0x31, 0x00]

theorem q06_length : q06.length = 7 := rfl

/-- The statement a header proves: `leafStmt h n` (`b = 0`) or `nodeStmt c' (leafStmt h n)`, with the
hashes given. -/
def stmtWith (leafS : Digest → Nat → Digest) (nodeS : Digest → Digest → Digest) (x : ByteArray) : Digest :=
  if Lvm.u64At x 8 = 0 then leafS (Lvm.digestAt x 24) (Lvm.u64At x 16)
  else nodeS (Lvm.digestAt x 56) (leafS (Lvm.digestAt x 24) (Lvm.u64At x 16))

/-- **The header check** (FORMAT6 v2.2 §2): the magic, `b ∈ {0, 1}`, `n = N★`, `b = 0 ⟹ c' = 0^32`, the key
`vk` at byte 88, and the statement, with the hashes given. -/
def hdrOkWith (leafS : Digest → Nat → Digest) (nodeS : Digest → Digest → Digest) (nStar : Nat) (vk c : Digest)
    (x : ByteArray) : Bool :=
  (List.range 8).all (fun i => x.get! i == magic6.getD i 0) && decide (Lvm.digestAt x 88 = vk) &&
    (Lvm.u64At x 8 == 0 || Lvm.u64At x 8 == 1) && Lvm.u64At x 16 == nStar &&
    (Lvm.u64At x 8 != 0 || decide (Lvm.digestAt x 56 = Lvm.zeroDigest)) &&
    decide (c = stmtWith leafS nodeS x)

/-- The statement of header bytes (the contract's hashes). -/
def stmtOf (x : List UInt8) : Digest := stmtWith leafStmt nodeStmt ⟨x.toArray⟩

/-- The seed's bytes after `a₀` (v2.5): `HDR` itself (`c` is bound by the executable check `c = stmtOf HDR`). -/
def enc6 (x : List UInt8) : List UInt8 := x

theorem enc6_injective : Function.Injective enc6 := fun _ _ h => h

/-- The header and the body of a proof. -/
def hdr6 (sh : VShape) (π : Proof) : Option (List UInt8 × List UInt8) :=
  if hdrLen sh ≤ π.size then some (π.data.toList.take (hdrLen sh), π.data.toList.drop (hdrLen sh)) else none

/-! ## The scheme -/

/-- **The specified scheme** of `V_S` for the decision `dec` (header bytes, transcript newest first). -/
def scheme6V (sh : VShape) (vk : Digest) (dec : List UInt8 → List Val → Bool) : Scheme where
  Stmt := List UInt8
  P := fun x => PS.walk sh.levs sh.sched [] [] fun _ acc => .ret (dec x acc)
  enc := enc6
  enc_inj := enc6_injective
  hdr := hdr6 sh
  ok := fun c x => hdrOkWith leafStmt nodeStmt sh.nStar vk c ⟨x.toArray⟩
  capOf := capOfL sh.levs
  q0 := q06
  q0_short := by decide
  decE := eOfBytes
  decK := kOfBytes
  chal := chalOf
  chal_sum := chalOf_sum
  occ := occL sh.levs
  rw := rwOf sh.sched
  rw_pos := rwOf_pos sh.sched

end Lvm6.V
