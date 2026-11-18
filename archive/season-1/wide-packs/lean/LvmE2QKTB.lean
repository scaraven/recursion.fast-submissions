-- New for lvm2 E2F (slice S1, E2F-QH1): the Keccak GKR verifier's template gadgets at `E2` (twin rows), the
-- `E2` counterparts of `LvmQKeccakTB`/`LvmQKeccakParts`/`LvmQKeccakParts2`.
import LvmQKeccakGkr
import LvmE2QIns
import LvmE2QBuild

/-!
# The Keccak GKR's template gadgets at `E2`

The `E3` gadgets of `LvmQKeccakTB`, `LvmQKeccakParts`, `LvmQKeccakParts2` written on `E2` operands (`S2`, a
pair of `K` sources `(re, im)`) with twin rows (`e2I`, `LvmE2QIns`). Every `E3` value of the layer's
arithmetic becomes an `E2` value (two `K` cells); a stream scalar is two `K` lanes read directly (`lane2`, no load
row); a `K` constant `k` enters an `E2` product as `(k, 0)` (`kS2`). Assertions are coordinatewise (`q2Assert`,
two `assert0` rows with the same gate).

The algebra is that of `V`'s `E2` front (`LvmE2VProg`, `LvmDecideE2` at `F = FE2`), which is the `E3` algebra over a
field parameter: the gadgets are those of `E3` one for one.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Primitives -/

/-- **A twin pair** of `f` on `xs`; its result is `(loc n, loc (n + 1))`. -/
def emit2 (f : E2Fn) (xs : List S2) : TB S2 := fun n => ((.loc n, .loc (n + 1)), e2I f xs)

/-- `a·b + d` in `E2`. -/
def q2Mul (a b d : S2) : TB S2 := emit2 .mul [a, b, d]

/-- `a + k·b + k'` in `E2` (`k ∈ K`, `k' ∈ E2`). -/
def q2Lin (k : FK) (k' : FE2) (a b : S2) : TB S2 := emit2 (.lin k k'.re k'.im) [a, b]

/-- `a + b`. -/
def q2Add (a b : S2) : TB S2 := q2Lin 1 0 a b

/-- `1 + a`. -/
def q2One (a : S2) : TB S2 := q2Lin 0 1 a a

/-- `k·a` for a constant `k ∈ K`. -/
def q2Scale (k : FK) (a : S2) : TB S2 := q2Lin (k + 1) 0 a a

/-- A copy of `a`. -/
def q2Copy (a : S2) : TB S2 := q2Lin 0 0 a a

/-- The gated assertion `gate·a = 0`, coordinatewise. -/
def q2Assert (a : S2) (gate : Src) : TB Unit := gAssert a.1 gate >>= fun _ => gAssert a.2 gate

/-- A `K` row `a + k·b + k'`. -/
def kLin (k k' : FK) (a b : Src) : TB Src := emit ⟨.lin k k', .K, [a, b]⟩

/-- A stream `E2` scalar: lanes `q` (re) and `q + 1` (im), moving by `str` per loop step. -/
def lane2 (q : Nat) (str : List Nat) : S2 := (.ext ⟨.K, q, str⟩, .ext ⟨.K, q + 1, str⟩)

/-- A `K` source as an `E2` operand, `z` a `K` zero. -/
def kS2 (k z : Src) : S2 := (k, z)

/-- A pair of cells as an operand. -/
def _root_.Lvm.Loop.Build.C2.s2 (c : C2) : S2 := (.ext c.re.addr, .ext c.im.addr)

/-- **The zeros**: from any `K` source `b`, a `K` zero `zK` (`b + b`), the `E2` zero `(zK, zK)` and the `E2` one
`(1 + zK, zK)` (two `K` rows). -/
def q2Base (b : Src) : TB (Src × S2 × S2) :=
  kLin 1 0 b b >>= fun zK => kLin 0 1 zK zK >>= fun oK => pure (zK, (zK, zK), (oK, zK))

/-! ## Lists -/

/-- Run a gadget per element. -/
def mapT2 {α β : Type} (f : α → TB β) : List α → TB (List β)
  | [] => pure []
  | a :: as => f a >>= fun x => mapT2 f as >>= fun xs => pure (x :: xs)

/-- `s + c₀ + c₁ + …`. -/
def q2Sum : S2 → List S2 → TB S2
  | s, [] => pure s
  | s, c :: cs => q2Add s c >>= fun s' => q2Sum s' cs

/-- `acc + Σ cᵢ·dᵢ`. -/
def q2Dot : S2 → List (S2 × S2) → TB S2
  | acc, [] => pure acc
  | acc, cd :: rest => q2Mul cd.1 cd.2 acc >>= fun a => q2Dot a rest

/-- Horner from the top coefficient `h`, then `cs` downwards. -/
def q2Horner (x : S2) : S2 → List S2 → TB S2
  | h, [] => pure h
  | h, c :: cs => q2Mul h x c >>= fun h' => q2Horner x h' cs

/-- One level of an `eq` table: `e·(1 + r)` for every `e`, then `e·r`. -/
def q2EqStep (z : S2) (tab : List S2) (r : S2) : TB (List S2) :=
  q2One r >>= fun r1 => mapT2 (fun e => q2Mul e r1 z) tab >>= fun lo =>
    mapT2 (fun e => q2Mul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- The `eq` table of a point from `tab`. -/
def q2EqTab (z : S2) : List S2 → List S2 → TB (List S2)
  | tab, [] => pure tab
  | tab, r :: rs => q2EqStep z tab r >>= fun t => q2EqTab z t rs

/-- `Σ_{c<k}` of per-index gadgets. -/
def q2SumMap (z : S2) (k : Nat) (f : Nat → TB S2) : TB S2 :=
  mapT2 f (List.range k) >>= fun ts => q2Sum z ts

/-! ## RMFE: projection and instance weights -/

/-- The weights summed for product coefficient `c`. -/
def projSrcs2 (masks : List Nat) (mu : List S2) (c : Nat) : List S2 :=
  (mu.zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none

/-- **The projection** `Σ_c (Σ_{i: mask_i ∋ c} μ_i)·product_c`. -/
def q2Proj (z : S2) (masks : List Nat) (mu prod : List S2) : TB S2 :=
  q2SumMap z prod.length fun c => q2Sum z (projSrcs2 masks mu c) >>= fun P => q2Mul P (prod.getD c default) z

/-- `acc, acc·s, …` (`k` terms). -/
def q2Powers (z s : S2) : S2 → Nat → TB (List S2)
  | _, 0 => pure []
  | acc, k + 1 => q2Mul acc s z >>= fun nx => q2Powers z s nx k >>= fun rest => pure (acc :: rest)

/-- The powers an embedding `e` sums. -/
def embSrcs2 (pw : List S2) (e : Nat) : List S2 :=
  (List.range embedBits).filterMap fun b => if e.testBit b then some (pw.getD b default) else none

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` and their sum `κ`. -/
def q2Inst (z one s : S2) (embs : List Nat) : TB (List S2 × S2) :=
  q2Powers z s one embedBits >>= fun pw => mapT2 (fun e => q2Sum z (embSrcs2 pw e)) embs >>= fun mu =>
    q2Sum z mu >>= fun kappa => pure (mu, kappa)

/-! ## RMFE by 4-bit tables (W32, lead D4)

At K = 32 the masks have 1,737 (projection) and 753 (embedding) set bits; one addition per bit doubles the layer. The
tables variant sums each group of four values once per subset (`q2Tab`) and reads one entry per group and column. -/

/-- The top bit of `m < 16` (`0` at `m = 0`). -/
def top4 (m : Nat) : Nat := if 8 ≤ m then 3 else if 4 ≤ m then 2 else if 2 ≤ m then 1 else 0

/-- `s` plus the list, without a leading zero (`z` when empty). -/
def q2SumL (z : S2) : List S2 → TB S2
  | [] => pure z
  | a :: as => q2Sum a as

/-- Entry `m ≥ 1` of a subset-sum table: `tab[m − 2^j] + v_j`, `j = top4 m` (no row for one bit). -/
def q2TabStep (v tab : List S2) (m : Nat) : TB (List S2) :=
  if m - 2 ^ top4 m = 0 then pure (tab ++ [v.getD (top4 m) default])
  else q2Add (tab.getD (m - 2 ^ top4 m) default) (v.getD (top4 m) default) >>= fun x => pure (tab ++ [x])

/-- Entries `m, m + 1, …` (`k` of them). -/
def q2TabGo (v : List S2) : List S2 → Nat → Nat → TB (List S2)
  | tab, _, 0 => pure tab
  | tab, m, k + 1 => q2TabStep v tab m >>= fun t => q2TabGo v t (m + 1) k

/-- **The subset-sum table** of `v` (`|v| ≤ 4`): entry `m = Σ_{j ∈ m} v_j`, entry `0` the zero `z`. -/
def q2Tab (z : S2) (v : List S2) : TB (List S2) := q2TabGo v [z] 1 (2 ^ v.length - 1)

/-- Four bits as a nibble. -/
def nib4 (b0 b1 b2 b3 : Bool) : Nat := b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat

/-- Column `c`'s nibble in mask group `g`: bit `j` is bit `c` of mask `4g + j`. -/
def nibP (masks : List Nat) (g c : Nat) : Nat :=
  nib4 ((masks.getD (4 * g) 0).testBit c) ((masks.getD (4 * g + 1) 0).testBit c)
    ((masks.getD (4 * g + 2) 0).testBit c) ((masks.getD (4 * g + 3) 0).testBit c)

/-- The table entries column `c` sums (one per group with a nonzero nibble). -/
def nibSrcsP (masks : List Nat) (tabs : List (List S2)) (c : Nat) : List S2 :=
  (List.range tabs.length).filterMap fun g =>
    if nibP masks g c = 0 then none else some ((tabs.getD g []).getD (nibP masks g c) default)

/-- `acc + Σ_c w_c·prod_c` from column `c` on (columns with no source skipped). -/
def q2ProjAcc (z : S2) (masks : List Nat) (tabs : List (List S2)) : List S2 → Nat → S2 → TB S2
  | [], _, acc => pure acc
  | p :: ps, c, acc =>
    if (nibSrcsP masks tabs c).isEmpty then q2ProjAcc z masks tabs ps (c + 1) acc
    else q2SumL z (nibSrcsP masks tabs c) >>= fun w => q2Mul w p acc >>= fun acc' =>
      q2ProjAcc z masks tabs ps (c + 1) acc'

/-- **The projection by 4-bit tables** (`|μ| = |masks| = 32`): the 8 tables of `μ`, then per column its entries. -/
def q2Proj4 (z : S2) (masks : List Nat) (mu prod : List S2) : TB S2 :=
  mapT2 (fun g => q2Tab z ((mu.drop (4 * g)).take 4)) (List.range 8) >>= fun tabs =>
  q2ProjAcc z masks tabs prod 0 z

/-- The powers group `g` of an embedding reads (`(pw.drop 4g).take 4`) and its nibble. -/
def embNib (pw : List S2) (e g : Nat) : Nat := (e >>> (4 * g)) % 2 ^ ((pw.drop (4 * g)).take 4).length

/-- **The instance weights by 4-bit tables of the powers of `s`** (14 groups of `embedBits = 53`) and their sum. -/
def q2Inst4 (z one s : S2) (embs : List Nat) : TB (List S2 × S2) :=
  q2Powers z s one embedBits >>= fun pw =>
  mapT2 (fun g => q2Tab z ((pw.drop (4 * g)).take 4)) (List.range 14) >>= fun tabs =>
  mapT2 (fun e => q2SumL z ((List.range 14).filterMap fun g =>
    if embNib pw e g = 0 then none else some ((tabs.getD g []).getD (embNib pw e g) default))) embs >>= fun mu =>
  q2SumL z mu >>= fun kappa => pure (mu, kappa)

/-! ## The shift tables, lane forms, flips, lane weights, `indexMle` -/

/-- `L_c(r_l)`. -/
def q2LowTab (z : S2) (ta tb : List S2) (c rl : Nat) : TB S2 :=
  q2SumMap z 8 fun zz => if (zz + rl) / 8 = c then q2Mul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

/-- `H(k)`. -/
def q2HighTab (z : S2) (ta tb : List S2) (k : Nat) : TB S2 :=
  q2SumMap z 8 fun zz => q2Mul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

/-- `shift(r) = L₀·H + L₁·H'`. -/
def q2Shift (z : S2) (L0 L1 H : List S2) (r : Nat) : TB S2 :=
  q2Mul (L1.getD (r % 8) default) (H.getD ((r / 8 + 1) % 8) default) z >>= fun t =>
    q2Mul (L0.getD (r % 8) default) (H.getD (r / 8) default) t

/-- `laneForm B R ℓ`. -/
def q2LaneForm (z : S2) (B : List S2) (R : Nat → S2) (l : Nat) : TB S2 :=
  q2Mul (B.getD (keccakPi l) default) (R (rho l)) z >>= fun t1 =>
  q2Dot t1 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) default, R (rho ((l % 5 + 1) % 5 + 5 * y)))) >>= fun t2 =>
  q2Dot t2 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) default, R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

/-- `flip_i = flipForm B A i`. -/
def q2Flip (z : S2) (B A : List S2) (i : Nat) : TB S2 :=
  q2LaneForm z B (fun s => A.getD ((iotaPos i + s) % 64) default) 0

/-- The next lane weights `eq_L(ℓ) + β(eq_L(x+4) + β eq_L(x+3))`. -/
def q2LaneW (eL : List S2) (beta : S2) : TB (List S2) :=
  mapT2 (fun l => q2Mul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default) >>= fun u => q2Mul beta u (eL.getD l default)) (List.range 25)

/-- One coordinate of `indexMle`: `acc·(1 + r·(1 + g^{2^k}))`. -/
def q2IndexStep (z : S2) (k : Nat) (acc r : S2) : TB S2 :=
  q2Scale (1 + FK.x ^ (2 ^ k)) r >>= fun u => q2One u >>= fun w => q2Mul acc w z

/-- `indexMleFrom (g^{2^k})` over the coordinates `rs`. -/
def q2Index (z : S2) : Nat → S2 → List S2 → TB S2
  | _, acc, [] => pure acc
  | k, acc, r :: rs => q2IndexStep z k acc r >>= fun acc' => q2Index z (k + 1) acc' rs

end Lvm.Q1
