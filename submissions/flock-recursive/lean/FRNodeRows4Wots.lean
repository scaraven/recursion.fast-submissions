-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.2 the WOTS mux rows, §4.4, A.6, A.7;
-- R-4-m2; stage S-E13b, track L-circ). 3.x: `FRWots` (`wots_chain_sound`, `digitSel_sound`).
import FRNodeCircuit4
import FRVIRTplCore
import FRRingSwitch

/-!
# The 4.1 node's WOTS rows and `aggPad` rows (S-N2's `Gap4.wots`, `Gap4.aggPad`)

Rows over the cells of `f` (H's blocks, `WM`'s mirrors, L's signature and bits, M's `one` and
selector copies) that make the circuit compute `SigOk vk m σ` on the digest `m` selected by an
aggregate's segment count, and R-4-m2's `k`-gated final block. The JOURNAL's §0 is the design
note; `FRNodeRows4WotsS` proves what the rows give.

**Cells.** `hc b e` is element `e` of H block `b` (`h_in` 0–1, `h_out` 2–3, message 4–7); WOTS
block `o` of signed child `σ` is `wotsB κ σ + o` (chain `i`'s step `s` at `3i + s`, key leaf block
`u` at `399 + u`, path `t` at `466 + 2t` (`hashB1`) and `467 + 2t` (`hashB2`)); mirror source `g`
(A.6) is elements `2 (g mod 4)`, `+1` of block `wmB κ σ + ⌊g/4⌋` (`mc`); L element `o` of signed
child `σ`'s stride is `Lc` (A.7: `idx` 0, `ots_i` `1 + 2i`, path `267 + 2t`, digit bits `299 + p`,
step selectors `565 + 3i + s`; the new bits and products from 8704, JOURNAL §0.1).

**Rows of signed child `σ`** (`wotsRows`):
* `idxRows`: the index's 16 bits, Boolean, `idx = Σ_t E_t b_t`, and the `j` family's mirror is
  `idx`;
* `selRows`: per chain the selectors `[d < 1] = (1 − b₀)(1 − b₁)`, `[d < 2] = 1 − b₁`,
  `1 − [d < 3] = b₀ b₁` (S-E2 F-2);
* `chainRows`: per chain `i`, the step inputs `x_{i,0} = ots_i`, `x_{i,s} − ots_i = [d < s]·
  (h_out(i, s − 1) − ots_i)` and the end `e_i − ots_i = [d < 3]·(h_out(i, 2) − ots_i)`, per
  element, on the `x`/`end9`/`end41` mirrors;
* `leafRows`: the key leaf's links `h_in(u + 1) = h_out(u)`;
* `pathRows`: per level `t`, `h_in(B2) = h_out(B1)`, `l − cur = b_t (sib − cur)`, `r − sib =
  b_t (cur − sib)` on the `l`/`r0` mirrors, and `r`'s byte 31 for the `r31` mirror through the
  128 bits of `r`'s element 1;
* `rootRows`: the last level's output is `vk` (the seed payload's cells, which `PubCells4` pins);
* `digRows`: the digest's 256 bits are the digit bits (`Σ_q E_q bit_{128h+q} = m_h`), with `m`
  the final block's `h_out`, muxed by the segment count for an aggregate (`ind j`);
* `sumRows`: the checksum, multiplicatively: `R_{i+1} = R_i · f_i` from `R_0 = 1` to `R_133 = 1`,
  `f_i = g^{3 − d_i}` for a message digit, `g^{−4^t c_t}` for checksum digit `t`.

**`aggPad` rows of aggregate `a`** (`padRows`): for each candidate `j < maxK`, gated by `ind j`,
`F_{a,j}`'s `h_in` is main block `aggL j − 2`'s `h_out` and its message is main block
`aggL j − 1`'s, whole (revision 4.4.1, R-A′: an aggregate stream fills its last block, `lastR = 64`,
so there is no padding and no element-7 decomposition; its L cells `pbC` hold the spacers' bits,
`FRNodeRows4Pack.spC`).
-/

namespace FR
namespace W4
open RecursionFast Rev4 Circ N4c

/-! ## Cells and row forms -/

/-- Element `e` of H block `b`. -/
def hc (b e : ℕ) : ℕ := b * 128 + e

/-- Element `h` of mirror source `g` of signed child `σ` (A.6's `WM` map). -/
def mc (κ : NodeKind) (σ g h : ℕ) : ℕ := (wmB κ σ + g / 4) * 128 + 2 * (g % 4) + h

/-- Element `o` of signed child `σ`'s L stride (A.7). -/
def Lc (κ : NodeKind) (σ o : ℕ) : ℕ := κ.lBase * 128 + σ * 2 ^ 14 + o

/-- The packing basis element `x^q` (`bitBasis`), `q < 128`. -/
def E (q : ℕ) : F := bitBasis ⟨q % 128, Nat.mod_lt _ (by norm_num)⟩

/-- M's `one`. -/
def one (κ : NodeKind) : Lin := Lin.cell κ.oneCell

/-- The constant `c`. -/
def cst (κ : NodeKind) (c : F) : Lin := [(κ.oneCell, c)]

/-- `x = y`. -/
def eqR (κ : NodeKind) (x y : Lin) : Row := ⟨one κ, x.sub y, []⟩

/-- Cell `c` is a bit. -/
def boolR (κ : NodeKind) (c : ℕ) : Row := ⟨Lin.cell c, (one κ).sub (Lin.cell c), []⟩

/-- `m − y = s (x − y)`: `m` is `x` when the bit `s` is `1`, `y` when it is `0`. -/
def muxR (s x y m : Lin) : Row := ⟨s, x.sub y, m.sub y⟩

/-- `s · x = 0`. -/
def gateR (s x : Lin) : Row := ⟨s, x, []⟩

/-- The bits `cell q`, `q < n`, packed: `Σ_q E_q · cell q`. -/
def pk (cell : ℕ → ℕ) (n : ℕ) : Lin := (List.range n).map fun q => (cell q, E q)

/-! ## The WOTS run's cells (signed child `σ`) -/

/-- WOTS block `o`. -/
def wb (κ : NodeKind) (σ o : ℕ) : ℕ := wotsB κ σ + o

/-- `ots_i`'s element `h`. -/
def otsC (κ : NodeKind) (σ i h : ℕ) : ℕ := Lc κ σ (1 + 2 * i + h)
/-- The path's sibling `t`, element `h`. -/
def sibC (κ : NodeKind) (σ t h : ℕ) : ℕ := Lc κ σ (1 + 2 * wotsLen + 2 * t + h)
/-- Digit bit `p` (digit `⌊p/2⌋`, bit `p mod 2`). -/
def digC (κ : NodeKind) (σ p : ℕ) : ℕ := Lc κ σ (299 + p)
/-- Chain `i`'s selector `[d_i < s + 1]`. -/
def selC (κ : NodeKind) (σ i s : ℕ) : ℕ := Lc κ σ (565 + 3 * i + s)
/-- The index bit `t`. -/
def ixC (κ : NodeKind) (σ t : ℕ) : ℕ := Lc κ σ (8704 + t)
/-- The checksum's running product `R_i` (`1 ≤ i ≤ 132`). -/
def prC (κ : NodeKind) (σ i : ℕ) : ℕ := Lc κ σ (8720 + i)
/-- Bit `q` of `r_t`'s element 1. -/
def rbC (κ : NodeKind) (σ t q : ℕ) : ℕ := Lc κ σ (8960 + 128 * t + q)
/-- The `k`-mux term `T_{j,h}` (`1 ≤ j ≤ 4`). -/
def tmC (κ : NodeKind) (σ j h : ℕ) : ℕ := Lc κ σ (11008 + 2 * (j - 1) + h)
/-- Revision 4.1's `aggPad` cells (bit `q` of main block `aggL j − 1`'s element 7, `2 ≤ j ≤ maxK`); since
R-A′ (whole blocks) the spacers' bits (`FRNodeRows4Pack.spC κ σ (j − 1) q`). -/
def pbC (κ : NodeKind) (σ j q : ℕ) : ℕ := Lc κ σ (11264 + 128 * (j - 2) + q)

/-- Chain `i`'s end mirror source: `end9` (`400 + i/2`) for an even end, `end41` (`467 + i/2`)
for an odd one. -/
def endG (i : ℕ) : ℕ := if i % 2 = 0 then 400 + i / 2 else 467 + i / 2

/-- The path's `cur_t`: the key leaf's output for `t = 0`, the previous level's `B2` after. -/
def curB (κ : NodeKind) (σ t : ℕ) : ℕ := if t = 0 then wb κ σ 465 else wb κ σ (467 + 2 * (t - 1))

/-! ## The rows -/

/-- The index: 16 Boolean bits, `idx = Σ E_t b_t`, the `j` mirror is `idx`. -/
def idxRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range 16).map (fun t => boolR κ (ixC κ σ t)) ++
    [eqR κ (Lin.cell (Lc κ σ 0)) (pk (ixC κ σ) 16), eqR κ (Lin.cell (mc κ σ 399 0)) (Lin.cell (Lc κ σ 0))]

/-- Chain `i`'s selectors from its digit bits. -/
def selRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range wotsLen).flatMap fun i =>
    let b₀ := Lin.cell (digC κ σ (2 * i)); let b₁ := Lin.cell (digC κ σ (2 * i + 1))
    [⟨(one κ).sub b₀, (one κ).sub b₁, Lin.cell (selC κ σ i 0)⟩,
     eqR κ (Lin.cell (selC κ σ i 1)) ((one κ).sub b₁),
     ⟨b₀, b₁, (one κ).sub (Lin.cell (selC κ σ i 2))⟩]

/-- Chain `i`'s step inputs and end, element `h`. -/
def chainRowsI (κ : NodeKind) (σ i h : ℕ) : List Row :=
  let ots := Lin.cell (otsC κ σ i h)
  let out := fun s => Lin.cell (hc (wb κ σ (3 * i + s)) (2 + h))
  [eqR κ (Lin.cell (mc κ σ (3 * i) h)) ots,
   muxR (Lin.cell (selC κ σ i 0)) (out 0) ots (Lin.cell (mc κ σ (3 * i + 1) h)),
   muxR (Lin.cell (selC κ σ i 1)) (out 1) ots (Lin.cell (mc κ σ (3 * i + 2) h)),
   muxR (Lin.cell (selC κ σ i 2)) (out 2) ots (Lin.cell (mc κ σ (endG i) h))]

def chainRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range wotsLen).flatMap fun i => (List.range 2).flatMap (chainRowsI κ σ i)

/-- The key leaf's links. -/
def leafRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range 66).flatMap fun u => (List.range 2).map fun h =>
    eqR κ (Lin.cell (hc (wb κ σ (400 + u)) h)) (Lin.cell (hc (wb κ σ (399 + u)) (2 + h)))

/-- Path level `t`: the link, the `l`/`r` mux, `r`'s byte 31. -/
def pathRowsT (κ : NodeKind) (σ t : ℕ) : List Row :=
  let b := Lin.cell (ixC κ σ t)
  (List.range 2).flatMap (fun h =>
    let cur := Lin.cell (hc (curB κ σ t) (2 + h)); let sib := Lin.cell (sibC κ σ t h)
    [eqR κ (Lin.cell (hc (wb κ σ (467 + 2 * t)) h)) (Lin.cell (hc (wb κ σ (466 + 2 * t)) (2 + h))),
     muxR b sib cur (Lin.cell (mc κ σ (533 + t) h)),
     muxR b cur sib (Lin.cell (mc κ σ (549 + t) h))]) ++
  (List.range 128).map (fun q => boolR κ (rbC κ σ t q)) ++
  [eqR κ (Lin.cell (mc κ σ (549 + t) 1)) (pk (rbC κ σ t) 128),
   eqR κ (Lin.cell (mc κ σ (565 + t) 0)) (pk (fun q => rbC κ σ t (120 + q)) 8)]

def pathRows (κ : NodeKind) (σ : ℕ) : List Row := (List.range sigHeight).flatMap (pathRowsT κ σ)

/-- The root is `vk` (the seed payload's `vk` cells). -/
def rootRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range 2).map fun h => eqR κ (Lin.cell (hc (wb κ σ 497) (2 + h))) (Lin.cell (seedC κ σ h))

/-- **The segment-count indicator** `[k = j]` (`1 ≤ j ≤ maxK`) from the sub-slots' activities `S`
(`S i` is sub-slot `i`'s activity, `1` for `i < k` and `0` after). -/
def ind (κ : NodeKind) (S : ℕ → Lin) (j : ℕ) : Lin := if j < κ.maxK then (S (j - 1)).sub (S j) else S (j - 1)

/-- The digest's bits are the digit bits: `m_h = Σ_q E_q bit_{128h+q}`, `m` the final block's
`h_out`, muxed by the segment count for an aggregate. -/
def digRows (κ : NodeKind) (σ : ℕ) (S : ℕ → Lin) : List Row :=
  if isAgg κ σ then
    (List.range κ.maxK).flatMap (fun j => (List.range 2).map fun h =>
      ⟨ind κ S (j + 1), Lin.cell (hc (finBlk κ σ (j + 1)) (2 + h)), Lin.cell (tmC κ σ (j + 1) h)⟩) ++
    (List.range 2).map fun h =>
      eqR κ ((List.range κ.maxK).map fun j => (tmC κ σ (j + 1) h, (1 : F))) (pk (fun q => digC κ σ (128 * h + q)) 128)
  else (List.range 2).map fun h =>
    eqR κ (Lin.cell (hc (finBlk κ σ 0) (2 + h))) (pk (fun q => digC κ σ (128 * h + q)) 128)

/-! ## The checksum -/

/-- **The checksum's generator** `g = x` (the base field's `x`; `ord g > 1023`,
`FRNodeRows4WotsS.gW_inj`). -/
def gW : F := ⟨⟨2⟩, 0⟩

/-- `(1 + u b₀)(1 + v b₁)` with `b₀ b₁ = 1 − s`: linear in `b₀, b₁, s` (times `c`). -/
def fac (κ : NodeKind) (c u v : F) (b₀ b₁ s : ℕ) : Lin :=
  [(κ.oneCell, c + c * u * v), (b₀, c * u), (b₁, c * v), (s, -(c * u * v))]

/-- Digit `i`'s factor: `g^{3 − d_i}` (message digits), `g^{−4^t c_t}` (checksum digit `t`). -/
def facI (κ : NodeKind) (σ i : ℕ) : Lin :=
  if i < 128 then fac κ (gW ^ 3) (gW⁻¹ - 1) (gW⁻¹ ^ 2 - 1) (digC κ σ (2 * i)) (digC κ σ (2 * i + 1)) (selC κ σ i 2)
  else fac κ 1 (gW⁻¹ ^ 4 ^ (i - 128) - 1) (gW⁻¹ ^ (2 * 4 ^ (i - 128)) - 1)
    (digC κ σ (2 * i)) (digC κ σ (2 * i + 1)) (selC κ σ i 2)

/-- The running product `R_i` (`R_0 = R_133 = one`). -/
def prL (κ : NodeKind) (σ i : ℕ) : Lin := if i = 0 ∨ i = wotsLen then one κ else Lin.cell (prC κ σ i)

def sumRows (κ : NodeKind) (σ : ℕ) : List Row :=
  (List.range wotsLen).map fun i => ⟨prL κ σ i, facI κ σ i, prL κ σ (i + 1)⟩

/-- **Signed child `σ`'s WOTS rows** (`S`: its aggregate's sub-slot activities). -/
def wotsRows (κ : NodeKind) (σ : ℕ) (S : ℕ → Lin) : List Row :=
  idxRows κ σ ++ selRows κ σ ++ chainRows κ σ ++ leafRows κ σ ++ pathRows κ σ ++ rootRows κ σ ++
    digRows κ σ S ++ sumRows κ σ

/-! ## `aggPad` (R-4-m2) -/

/-- The bytes of the last block of a `k`-segment stream (`64` for `k = 1 … 4`: R-A′'s whole blocks). -/
def lastR (k : ℕ) : ℕ := aggB k - 64 * (aggL k - 1)

/-- Main block `i` of signed child `σ`. -/
def mb (κ : NodeKind) (σ i : ℕ) : ℕ := chBase κ σ + i

/-- **Aggregate `a`'s `aggPad` rows** (`σ = aggChild κ a`, `S` its sub-slots' activities): for each
candidate `j < maxK`, gated by `[k = j]`, `F_{a,j}`'s `h_in` (elements 0–1) and its message (elements
4–7, the whole block) are the main chain's. -/
def padRows (κ : NodeKind) (a : ℕ) (S : ℕ → Lin) : List Row :=
  let σ := aggChild κ a
  (List.range (κ.maxK - 1)).flatMap fun j' =>
    let j := j' + 1
    let F := finBlk κ σ j
    (List.range 2).map (fun h =>
      gateR (ind κ S j) ((Lin.cell (hc F h)).sub (Lin.cell (hc (mb κ σ (aggL j - 2)) (2 + h))))) ++
    (List.range 4).map (fun e =>
      gateR (ind κ S j) ((Lin.cell (hc F (4 + e))).sub (Lin.cell (hc (mb κ σ (aggL j - 1)) (4 + e)))))

/-! ## Facts and controls -/

theorem lastR_eq : lastR 1 = 64 ∧ lastR 2 = 64 ∧ lastR 3 = 64 ∧ lastR 4 = 64 := by decide

end W4
end FR
