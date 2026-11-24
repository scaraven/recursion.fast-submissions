-- New for lvm6 (WP CB). The frozen statements of the child-verification circuit's Keccak family:
-- the node circuit's re-execution of the child's tree batch, sponge caller and sponge link
-- (`docs/lvm6/stages/CB-circuit.md`). Season 1's builder (`Lvm.Loop.Build`, `BM`), its `E2` kit
-- (`LvmE2QWKit`) and its gadget logic (`HsA`, `LvmE2QLSem`), as CA uses them.
import Lvm6KStmt
import Lvm6Format
import LvmE2QLSem
import LvmFieldE2Correct

/-!
# CB's frozen statements

**The `V` side is K1's DSL programs.** The node circuit re-executes the child's Keccak phases:
`treeProg κ` (FORMAT6 §6.2), `spCaller6 h` (§6.3 with §T's caller) and season 1's
`ksLinkProgE2` (§T's link). A HAR (honest arithmetisation relation) says: on a memory where the
gadget's rows and gated assertions hold (`HsA`, gate `1`), for every event list whose
observables are the stream lanes (`EvMatch`) and whose ground draws pass their grinds on the PoW
lane (`PowLay`), the program **returns** after exactly those events (`after evs = some (ret out)`)
and the gadget's output cells are `out`'s fields (`Rep`). With `after_bind_append` the phases
compose along the child's whole program, so `node6` chains them in schedule order.

* **Stream geometry** (FORMAT6 §3, §4): an entry is `enc64 |q|` (1 lane), the query, the answer
  (4 lanes); a chain query is `st` (4 lanes) then `buf`. `layItems its a` lays FORMAT6 items
  (`Lvm6.Item`, WP-S's type) from the lane `a` of the current entry's `buf`: `E k` = `k` scalars
  of 2 lanes, `K k` = `k` lanes, `G g` = the nonce lane, then the answer (next entry's `buf` 10
  lanes on), `D k` = `k` answers with empty `buf` (9 lanes apart).
* **Events** (`LEv`): `e a` an `E2` scalar at lanes `a, a+1`; `k a` an 8-byte word at `a` (a `K`
  word or a nonce); `d a g` a draw whose answer starts at `a`, its PoW lane `a + 2` at grind `g`
  (`g = 0`: further draw, no check). `EvMatch` asks only what the programs observe (`e2OfE` of a
  scalar, lane 0 of a word, the three lanes of an answer), so it holds for any codec that puts the
  stream bytes into those limbs.
* **The statements** take the generator as an argument (CB's gadgets land against them, a proof
  never changes them): `TreeHarStmt G` (CB-1), `SpHarStmt G` (CB-2), `LinkHarStmt G` (CB-3).
  `treeItems κ`, `spItems h` are WP-S's `treePart`/`keccakCore` at `κ`, so the layouts follow
  `sched6` (`treeItems_P18`: equal to `P18.treePart`, by `decide`).

Category: the programs and `Lvm6.Item` are frozen elsewhere (K1, S); `layItems`, `EvMatch`,
`PowLay`, `Har` and the `Rep` relations are Category A (specification of intent, CB).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K
open Lvm6 (Item rep rnd)

/-! ## Stream geometry and events -/

/-- An event slot of a phase: an `E2` scalar at lanes `a, a+1`; an 8-byte word at `a`; a draw
whose answer starts at `a` (PoW lane `a + 2`) at grind `g`. -/
inductive LEv where
  | e (a : ℕ)
  | k (a : ℕ)
  | d (a g : ℕ)
  deriving DecidableEq, Repr

/-- The further draws of `pos i g` at `P18` (`draws − 1`). -/
def posD (i : ℕ) : ℕ := (P18.levs.getD i default).draws - 1

/-- The lanes of `cap i` at `P18`: `32·2^lv` bytes. -/
def capL (i : ℕ) : ℕ := 4 * 2 ^ (P18.levs.getD i default).lv

/-- **The event slots of FORMAT6 items** laid from lane `a` (the current entry's `buf`): `G g`'s
nonce at `a`, its answer at `a + 1`, the next `buf` at `a + 10`; a further draw's answer at `a`,
the next `buf` at `a + 9`; a bind `B` is one such draw (grind 0, value ignored). `pos i g` is laid as
V1's walk reads it (FORMAT6 v2.5.3 §5, CA2's `itOfs`): its ground group `G g`, then `D(draws − 1)`
(`posD i`, level `i` of `P18`); a cap `cap i` occupies its `4·2^lv` lanes (its bytes are buffered into the
next query, V1's `fsLensAux`) and is not an event; an opening is laid by CC's `openStride` geometry (no
lanes here). WP NODE's `laneChk_P18` checks these lane counts against the plan of `sched6 P18`. Caps,
openings and positions do not occur in the Keccak phases. -/
def layItems : List Item → ℕ → List LEv
  | [], _ => []
  | .E n :: its, a => (List.range n).map (fun i ↦ LEv.e (a + 2 * i)) ++ layItems its (a + 2 * n)
  | .K n :: its, a => (List.range n).map (fun i ↦ LEv.k (a + i)) ++ layItems its (a + n)
  | .G g :: its, a => [LEv.k a, LEv.d (a + 1) g] ++ layItems its (a + 10)
  | .D n :: its, a => (List.range n).map (fun i ↦ LEv.d (a + 9 * i) 0) ++ layItems its (a + 9 * n)
  | .B :: its, a => [LEv.d a 0] ++ layItems its (a + 9)
  | .pos i g :: its, a => [LEv.k a, LEv.d (a + 1) g] ++
      ((List.range (posD i)).map (fun j ↦ LEv.d (a + 10 + 9 * j) 0) ++ layItems its (a + 10 + 9 * posD i))
  | .cap i :: its, a => layItems its (a + capL i)
  | .open _ :: its, a => layItems its a

/-- The lane after the items (the next `buf`). -/
def layEnd : List Item → ℕ → ℕ
  | [], a => a
  | .E n :: its, a => layEnd its (a + 2 * n)
  | .K n :: its, a => layEnd its (a + n)
  | .G _ :: its, a => layEnd its (a + 10)
  | .D n :: its, a => layEnd its (a + 9 * n)
  | .B :: its, a => layEnd its (a + 9)
  | .pos i _ :: its, a => layEnd its (a + 10 + 9 * posD i)
  | .cap i :: its, a => layEnd its (a + capL i)
  | .open _ :: its, a => layEnd its a

/-- A `K` cell's word in the DSL's field. -/
def lk (M : Mem) (a : ℕ) : K := FK.toBF64 (M.k a)

/-- A `K`-typed cell's word. -/
def kv (M : Mem) (x : Cell) : K := FK.toBF64 (x.val M).c₀

/-- An `E2` operand's value in the DSL's field. -/
def ev2 (M : Mem) (x : C2) : E2 := FE2.toE2 (x.val M)

/-- **One event matches its slot**: the observables of the event are the stream lanes. -/
def EvM (M : Mem) : LEv → Ev → Prop
  | .e a, .read x => e2OfE x = ev2 M (ld2 a)
  | .k a, .read x => x.limb 0 = lk M a
  | .d a _, .sample x => x.limb 0 = lk M a ∧ x.limb 1 = lk M (a + 1) ∧ x.limb 2 = lk M (a + 2)
  | _, _ => False

/-- **The events match the slots**, one for one, in order. -/
def EvMatch (M : Mem) (lay : List LEv) (evs : List Ev) : Prop := List.Forall₂ (EvM M) lay evs

/-- **Every ground draw of the slots passes its grind** on its PoW lane (`< 2^(64−g)`). -/
def PowLay (M : Mem) (lay : List LEv) : Prop :=
  ∀ a g, LEv.d a g ∈ lay → kToNat (lk M (a + 2)) < 2 ^ (64 - g)

/-- **A HAR**: with the gate on, where the gadget's rows and assertions hold, every matching event
list with passing grinds makes the program return, and the outputs are represented. -/
def Har {α β : Type} (gate : Cell) (g : BM α) (prog : VerifierProgram β) (lay : List LEv)
    (Rep : Mem → α → β → Prop) : Prop :=
  ∀ (c : Ctx) (M : Mem), gate.val M = 1 → HsA c M g fun o ↦
    PowLay M lay → ∀ evs, EvMatch M lay evs → ∃ out, prog.after evs = some (.ret out) ∧ Rep M o out

/-! ## The phases' items (WP-S's lists at `κ`) -/

/-- The tree batch's items for `2^κ` rows (§6.2 rows 1–10): `P18.treePart` at `κ`. -/
def treeItems (κ : ℕ) : List Item := Shape.treePart { P18 with logN := κ - 1, κ := κ }

/-- The reduction core of a batch of `2^κ` rows (§6.2 rows 6–10, `top` for the tree). -/
def coreItems (κ : ℕ) (top : Bool) : List Item := P18.keccakCore κ top

/-- **§T, the sponge caller** (frozen by CB): `h` ground draws `G(1)`, the 25 output scalars. -/
def spCallerItems (h : ℕ) : List Item := rep h [.G 1] ++ [.E 25]

/-- The sponge caller and its core (§6.3). -/
def spItems (h : ℕ) : List Item := spCallerItems h ++ coreItems h false

/-- **§T, the sponge link** (frozen by CB): `hk + 5` ground draws `G(1)`, `hk` plain rounds
`R(2, 2)`, the four values `E(4)` (season 1's `ksLinkProgE2`). -/
def linkItems (hk : ℕ) : List Item := rep (hk + 5) [.G 1] ++ rep hk (rnd 2 2) ++ [.E 4]

/-- The tree items at the season's shape are WP-S's. -/
theorem treeItems_P18 : treeItems 19 = P18.treePart := rfl

/-- The sponge core at the season's shape is WP-S's. -/
theorem coreItems_P18 : coreItems 13 false = P18.keccakCore P18.κs false := rfl

/-! ## What the gadgets hand on -/

/-- **The tree gadget's outputs** (the cells of `TreeOut`'s fields that `treeCols` and the slice
claims read): `δ` (`K` cells), `ρ`, `D⁰ D¹`, `u`, the middle opening's point and word, the slice
point and the 64 slices. -/
structure TreeOutC where
  δ : List Cell
  ρ : List C2
  dd : List C2
  u : C2
  ϱm : List C2
  cout : C2
  pt : List C2
  s : List C2

/-- The tree gadget's cells represent the program's output. -/
def TreeRep (M : Mem) (o : TreeOutC) (out : Lvm6.K.TreeOut) : Prop :=
  o.δ.map (kv M) = out.δ ∧ o.ρ.map (ev2 M) = out.ρ ∧ o.dd.map (ev2 M) = out.dd ∧
    ev2 M o.u = out.u ∧ o.ϱm.map (ev2 M) = out.hd.ϱm ∧ ev2 M o.cout = out.hd.cout ∧
    o.pt.map (ev2 M) = out.en.pt ∧ o.s.map (ev2 M) = out.en.s

/-- **The sponge caller gadget's outputs**: `r`, the 25 output scalars, the middle opening's point
and word, the slice point and the slices (what `SpongeClaims` reads). -/
structure SpOutC where
  r : List C2
  v : List C2
  ϱm : List C2
  cout : C2
  pt : List C2
  s : List C2

/-- The sponge caller gadget's cells represent the program's output. -/
def SpRep (M : Mem) (o : SpOutC) (out : SpOut) : Prop :=
  o.r.map (ev2 M) = out.1 ∧ o.v.map (ev2 M) = out.2.1 ∧ o.ϱm.map (ev2 M) = out.2.2.1.ϱm ∧
    ev2 M o.cout = out.2.2.1.cout ∧ o.pt.map (ev2 M) = out.2.2.2.pt ∧ o.s.map (ev2 M) = out.2.2.2.s

/-- **The sponge link gadget's outputs**: the `hk + 5` challenges, the shift point and final
claim, the four values `Y, in, M, X` (what `KsClaimsE2` reads). -/
structure LinkOutC where
  kchal : List C2
  shift : List C2
  final : C2
  vals : List C2

/-- The link gadget's cells represent the program's output. -/
def LinkRep (M : Mem) (o : LinkOutC) (out : List E2 × (List E2 × E2) × List E2) : Prop :=
  o.kchal.map (ev2 M) = out.1 ∧ o.shift.map (ev2 M) = out.2.1.1 ∧ ev2 M o.final = out.2.1.2 ∧
    o.vals.map (ev2 M) = out.2.2

/-! ## The frozen HAR statements -/

/-- **CB-1, the tree batch** (statement): the generator `G κ a gate` (lanes from `a`, gated by
`gate`) re-executes `treeProg κ` on the stream laid out by `treeItems κ`. -/
def TreeHarStmt (G : ℕ → ℕ → Cell → BM TreeOutC) : Prop :=
  ∀ κ, 5 ≤ κ → ∀ (a : ℕ) (gate : Cell),
    Har gate (G κ a gate) (treeProg κ) (layItems (treeItems κ) a) TreeRep

/-- **CB-2, the sponge caller** (statement): `G h a gate` re-executes `spCaller6 h`. -/
def SpHarStmt (G : ℕ → ℕ → Cell → BM SpOutC) : Prop :=
  ∀ h, 5 ≤ h → ∀ (a : ℕ) (gate : Cell),
    Har gate (G h a gate) (spCaller6 h) (layItems (spItems h) a) SpRep

/-- **CB-3, the sponge link** (statement): `G hk xl B K a gate` re-executes season 1's
`ksLinkProgE2 hk xl rows` with `rows = [1, B) ∪ [K + 1, K + 32)` (`rowsBK B K`). -/
def LinkHarStmt (G : ℕ → ℕ → ℕ → ℕ → ℕ → Cell → BM LinkOutC) : Prop :=
  ∀ (hk xl B K : ℕ), B - 1 < 2 ^ hk → K + 31 < 2 ^ hk → ∀ (a : ℕ) (gate : Cell),
    Har gate (G hk xl B K a gate) (ksLinkProgE2 hk xl (rowsBK B K)) (layItems (linkItems hk) a)
      LinkRep

end Lvm6.QK
