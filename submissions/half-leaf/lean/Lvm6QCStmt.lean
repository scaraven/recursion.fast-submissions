-- New for lvm6 (WP CC). The frozen statements of the child-verification circuit's opening family:
-- the node circuit's re-execution of the child's affine-fold WHIR opening (W1's programs `roundP`,
-- `roundsP`, `tailP`, `levelP` at `chalE2`) and of ring switching with the stacked-claim batch
-- (RS's `ringProg`, `stackClaim`, `ringWeight`), in CB's HAR form (`docs/lvm6/stages/CC-circuit.md`).
import Lvm6QKStmt
import Lvm6Whir
import Lvm6WhirE2
import Lvm6Ring
import Lvm6AsmRing
import Lvm6WhirPos
import Lvm6WhirLanes

/-!
# CC's frozen statements

**Slots.** CB's event slots (`LEv`: a scalar, a word, a draw) do not cover the opening's other two
events, so CC adds them around CB's type (`OEv`): `.b l` is CB's slot `l` with CB's match `EvM`;
`.c ht wd` matches a commitment of that shape (the cap is absorbed into the chain buffer, the
committed word is not observed); `.o rows` matches an opening whose rows are trace lanes (`some a`)
or zero words (`none`, the 18 padding lanes of a level-0 row, FORMAT6 §5). `OEvMatch`, `PowLayO` and
`HarO` are CB's `EvMatch`, `PowLay` and `Har` over these slots (`Har` is `HarO` on `.b` slots:
`Lvm6QCRun.harO_map_b`).

**Geometry** (FORMAT6 v2.2.1 §4–§6.6, CB's lane conventions: the lane `a` is the current entry's
`buf`). A fold round `E(4)·G(g)·D(1)` takes 27 lanes. A bind `B` is a draw at `a` (next `buf` at
`a + 9`). A cap of `2^lv` nodes is `4·2^lv` lanes of `buf`. The openings of a level are entries of
the trace, not absorbed: opening `k`'s leaf word `j` is at `a − 4 + k·stride + j`, with
`stride = leafB/8 + 5 + 13·(ht − lv)` (leaf entry, then `ht − lv` node entries of 13 lanes); the next
`buf` is at `a + t·stride`. A row has `wd − leafB/8` zero words, then the leaf's words in leaf order
(level 0: `wd = 64`, 46 words; levels 1–4: `wd = 32`, 32 words, no padding).

**The statements** take the generator as an argument (CB's style; a proof never changes them):
`RoundHarStmt` (CC-1), `RoundsHarStmt` (CC-2), `TailHarStmt` (CC-3, the level interface: high part,
next cap, `B`, OOD group, `y`, query group, openings; the positions and the opened values are the
gadgets `posG`, `valsG` against the code facts' `pos` and the verifier's `vals`, `PosOK`, `ValsAt`),
`LevelHarStmt` (CC-4), `RingHarStmt` (CC-5, RS's one-map group), `RingPhaseHarStmt` (CC-5′, ASM's
`ringPhase6`: `B`, two maps, `λ₀`, the batched value), `RingValStmt` (CC-6, the batched
claim's value in RS's order, at most `J₀` claims), `RingTargetStmt` and `BatchValStmt` (CC-6a/b, the
same in any order), `RingWeightStmt` (CC-7, the ring claim's weight at a point).

Category: the programs, `Level`, `Claim` are frozen elsewhere (W1, RS, S); `OEv`, the layouts, the
`Rep`s, `PosOK`, `ValsAt` and the statements are Category A (specification of intent, CC).
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level)

/-! ## Slots -/

/-- **An event slot of the opening family**: CB's slot, a commitment of `2^ht` rows of `wd` words,
or an opening whose rows are lanes (`some a`) or zero words (`none`). -/
inductive OEv where
  | b (l : LEv)
  | c (ht wd : ℕ)
  | o (rows : List (List (Option ℕ)))
  deriving DecidableEq, Repr

/-- The word of a row entry: the lane's word, or `0`. -/
def lw (M : Mem) : Option ℕ → K
  | none => 0
  | some a => lk M a

/-- The rows an opening slot reads. -/
def rowsOf (M : Mem) (rows : List (List (Option ℕ))) : List (List K) := rows.map (·.map (lw M))

/-- **One event matches its slot**: CB's match on `.b`; a commitment of the slot's shape; an opening
whose rows are the slot's words. -/
def OEvM (M : Mem) : OEv → Ev → Prop
  | .b l, e => EvM M l e
  | .c ht wd, .commit ht' wd' _ => ht' = ht ∧ wd' = wd
  | .o rows, .query rs => rs = rowsOf M rows
  | _, _ => False

/-- **The events match the slots**, one for one, in order. -/
def OEvMatch (M : Mem) (lay : List OEv) (evs : List Ev) : Prop := List.Forall₂ (OEvM M) lay evs

/-- **Every ground draw of the slots passes its grind** on its PoW lane. -/
def PowLayO (M : Mem) (lay : List OEv) : Prop :=
  ∀ a g, OEv.b (LEv.d a g) ∈ lay → kToNat (lk M (a + 2)) < 2 ^ (64 - g)

/-- **A HAR over the opening slots** (CB's `Har` with `OEv`). -/
def HarO {α β : Type} (gate : Cell) (g : BM α) (prog : VerifierProgram β) (lay : List OEv)
    (Rep : Mem → α → β → Prop) : Prop :=
  ∀ (c : Ctx) (M : Mem), gate.val M = 1 → HsA c M g fun o ↦
    PowLayO M lay → ∀ evs, OEvMatch M lay evs → ∃ out, prog.after evs = some (.ret out) ∧ Rep M o out

/-! ## Geometry -/

/-- CB's slots as opening slots. -/
def bl (l : List LEv) : List OEv := l.map OEv.b

/-- The row width of commitment `i` (FORMAT6 v2.2.1, F1): `64` at level 0, `32` at levels `1–4`. -/
def wdOf (i : ℕ) : ℕ := if i = 0 then 64 else 32

/-- The lanes of one opening in the trace: the leaf entry and `ht − lv` node entries. -/
def openStride (lev : Level) : ℕ := lev.leafB / 8 + 5 + 13 * (lev.ht - lev.lv)

/-- Opening `k`'s row (`b` = lane of the first opening's leaf word 0): `wd − leafB/8` zero
words, then the leaf's words. -/
def openRow (lev : Level) (wd b k : ℕ) : List (Option ℕ) :=
  List.replicate (wd - lev.leafB / 8) none ++
    (List.range (lev.leafB / 8)).map fun j ↦ some (b + k * openStride lev + j)

/-- The rows of `t` openings. -/
def openRows (lev : Level) (wd b t : ℕ) : List (List (Option ℕ)) :=
  (List.range t).map (openRow lev wd b)

/-- **A fold round** from lane `a`: `E(4)`, `G(g)` (`α`), `D(1)` (`β`); 27 lanes. -/
def layRound (g a : ℕ) : List OEv := bl (layItems [.E 4, .G g, .D 1] a)

/-- `ℓ` fold rounds from lane `a`. -/
def layRounds (g : ℕ) : ℕ → ℕ → List OEv
  | 0, _ => []
  | ℓ + 1, a => layRound g a ++ layRounds g ℓ (a + 27)

/-- The lane after the tail's query group (the openings' cursor). -/
def tailOpenAt (nh ko kq lvN a : ℕ) : ℕ := a + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 + 10 + 9 * (kq + 1)

/-- **The level interface** from lane `a` (FORMAT6 v2.2.1 §6.6, W1's `tailP` order): the high part
`E(nh)`, the next cap (`2^lvN` nodes, commitment `(ht, wd)`), the bind `B`, the OOD group `G(gO)`
`D(ko)`, `E(1)` (`y`), the query group `G(gQ)` `D(kq + 1)`, the `t` openings of `lev` at width `wdI`. -/
def layTail (nh ko kq t : ℕ) (lev : Level) (wdI ht wd lvN gO gQ a : ℕ) : List OEv :=
  let a2 := a + 2 * nh + 4 * 2 ^ lvN
  bl (layItems [.E nh] a) ++ [.c ht wd] ++ [.b (.d a2 0)] ++
    bl (layItems [.G gO, .D ko, .E 1, .G gQ, .D (kq + 1)] (a2 + 9)) ++
    [.o (openRows lev wdI (tailOpenAt nh ko kq lvN a - 4) t)]

/-- **The ring group** from lane `a`: `G(g)`, `D(16)` (RS's `ringProg`: `f`, `g`, `λ₀`). -/
def layRing (g a : ℕ) : List OEv := bl (layItems [.G g, .D 16] a)

/-- **The ring phase** (ASM's `ringPhase6`, FORMAT6 v2.4 §6.5) from lane `a`: the bind `B` (a draw at
`a`), then `G(g)`, `D(32)` (tree `f, g`, sponge `f, g`, `λ₀`). -/
def layRing6 (g a : ℕ) : List OEv := [.b (.d a 0)] ++ bl (layItems [.G g, .D 32] (a + 9))

/-! ## What the gadgets hand on -/

/-- A fold round's cells. -/
structure RndC where
  u₀ : C2
  w : C2
  c₀ : C2
  c₁ : C2
  α : C2
  β : C2

/-- The round's cells represent the program's round. -/
def RndRep (M : Mem) (o : RndC) (r : Whir.Rnd E2) : Prop :=
  ev2 M o.u₀ = r.u₀ ∧ ev2 M o.w = r.w ∧ ev2 M o.c₀ = r.c₀ ∧ ev2 M o.c₁ = r.c₁ ∧
    ev2 M o.α = r.α ∧ ev2 M o.β = r.β

/-- The rounds' cells represent the program's rounds. -/
def RndsRep (M : Mem) (o : List RndC) (rs : List (Whir.Rnd E2)) : Prop :=
  List.Forall₂ (RndRep M) o rs

/-- The level interface's cells: the high part, the OOD point, `y`, the positions (`K` cells whose
word's `u64` is the position, i.e. the domain point `K(p)`), `λ`, the opened values. -/
structure TailOutC where
  hi : List C2
  z : List C2
  y : C2
  ps : List Cell
  lam : C2
  c : List C2

/-- The positions a list of `K` cells holds. -/
def posOf (M : Mem) (ps : List Cell) : List ℕ := ps.map fun x ↦ kToNat (kv M x)

/-- The interface's cells represent the program's output. -/
def TailRep {ko t n : ℕ} (M : Mem) (o : TailOutC) (out : Whir.TailOut E2 ko t n) : Prop :=
  o.hi.map (ev2 M) = out.hi ∧ o.z.map (ev2 M) = List.ofFn out.z ∧ ev2 M o.y = out.y ∧
    posOf M o.ps = List.ofFn (fun k ↦ (out.ps k : ℕ)) ∧ ev2 M o.lam = out.lam ∧
    o.c.map (ev2 M) = List.ofFn out.c

/-- The level's cells represent the program's rounds and interface. -/
def LevelRep {ko t n : ℕ} (M : Mem) (o : List RndC × TailOutC)
    (out : List (Whir.Rnd E2) × Whir.TailOut E2 ko t n) : Prop :=
  RndsRep M o.1 out.1 ∧ TailRep M o.2 out.2

/-- The ring group's cells: `f`, `g`, `λ₀`. -/
structure RingC where
  f : List C2
  g : List C2
  lam : C2

/-- The ring group's cells represent the program's output. -/
def RingRep (M : Mem) (o : RingC) (out : List E2 × List E2 × E2) : Prop :=
  o.f.map (ev2 M) = out.1 ∧ o.g.map (ev2 M) = out.2.1 ∧ ev2 M o.lam = out.2.2

/-- The ring phase's cells: the tree and sponge maps, `λ₀`, the batched claim's value. -/
structure RingPhC where
  ft : List C2
  gt : List C2
  fs : List C2
  gs : List C2
  lam : C2
  val : C2

/-- The ring phase's cells represent its output: the claim is ASM's `claimOf6` at the cells' maps
and `λ₀` (so its weight is CC-7's at those cells), and the value cell is the claim's value. -/
def RingPhRep (sl : List SliceClaim) (st : List StackClaim6) (M : Mem) (o : RingPhC)
    (out : StackClaim6) : Prop :=
  out = claimOf6 sl st (((o.ft.map (ev2 M), o.gt.map (ev2 M)), (o.fs.map (ev2 M), o.gs.map (ev2 M))),
    ev2 M o.lam) ∧ ev2 M o.val = out.2

/-! ## The gadgets the level interface is built from -/

/-- **A position gadget** computes the code's positions from the draws' cells. -/
def PosOK {n t kq : ℕ} (pos : (Fin (kq + 1) → E2) → Fin t → Fin n)
    (G : (Fin (kq + 1) → C2) → Cell → BM (List Cell)) : Prop :=
  ∀ (c : Ctx) (M : Mem) (ds : Fin (kq + 1) → C2) (gate : Cell), gate.val M = 1 →
    HsA c M (G ds gate) fun ps ↦ posOf M ps = List.ofFn fun k ↦ (pos (fun j ↦ ev2 M (ds j)) k : ℕ)

/-- **A value gadget at a memory** computes the verifier's values `vals` from the high part's
cells, the position cells and the opened rows. -/
def ValsAt {n t : ℕ} (c : Ctx) (M : Mem)
    (vals : List E2 → (Fin t → Fin n) → List (List K) → Fin t → E2)
    (G : List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2)) : Prop :=
  ∀ (hi : List C2) (ps : List Cell) (rows : List (List (Option ℕ))) (gate : Cell), gate.val M = 1 →
    HsA c M (G hi ps rows gate) fun cs ↦ ∀ p : Fin t → Fin n,
      posOf M ps = List.ofFn (fun k ↦ (p k : ℕ)) →
        cs.map (ev2 M) = List.ofFn (vals (hi.map (ev2 M)) p (rowsOf M rows))

/-- **CC-3a, the deployed position gadget** (statement, W1's `posE2`, FORMAT6 §5): `G h c kq t`
computes the `t` positions (`c` digits of `h` bits per draw, `c·h ≤ 128`) of the `kq + 1` draws as
`K` cells holding `K(p)`. Correction (CC, before any proof): `h ≤ 64` added, since a `K` cell
holds at most 64 bits (deployed `h ≤ 21`); without it the statement is false at `c = 1, h > 64`. -/
def PosE2Stmt (G : ℕ → ℕ → (kq : ℕ) → ℕ → (Fin (kq + 1) → C2) → Cell → BM (List Cell)) : Prop :=
  ∀ (h c kq t : ℕ) (hc : 0 < c) (ht : t ≤ (kq + 1) * c), c * h ≤ 128 → h ≤ 64 →
    PosOK (Whir.posE2 h c (kq + 1) t hc ht) (G h c kq t)

/-- **CC-3b, the deployed value gadget** (statement, W1's `valsE`): `G z h ℓ κ rc` computes a mid
level's opened values (each row folded by the rounds the cells `rc` represent, minus the high part
at `K(p)`). -/
def ValsEStmt (G : Bool → ℕ → ℕ → ℕ → List RndC → List C2 → List Cell → List (List (Option ℕ)) →
    Cell → BM (List C2)) : Prop :=
  ∀ (z : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) (t : ℕ) (c : Ctx) (M : Mem) (rc : List RndC)
    (rs : List (Whir.Rnd E2)), RndsRep M rc rs →
      ValsAt (t := t) c M (Whir.valsE z h ℓ κ hh rs) (G z h ℓ κ rc)

/-! ## The frozen HAR statements -/

/-- **CC-1, a fold round** (statement): `G g a gate` re-executes W1's `roundP chalE2 g`. -/
def RoundHarStmt (G : ℕ → ℕ → Cell → BM RndC) : Prop :=
  ∀ g, g ≤ 64 → ∀ (a : ℕ) (gate : Cell),
    HarO gate (G g a gate) (Whir.roundP Whir.chalE2 g) (layRound g a) RndRep

/-- **CC-2, a level's fold rounds** (statement): `G g ℓ a gate` re-executes `roundsP chalE2 g ℓ`. -/
def RoundsHarStmt (G : ℕ → ℕ → ℕ → Cell → BM (List RndC)) : Prop :=
  ∀ g, g ≤ 64 → ∀ (ℓ a : ℕ) (gate : Cell),
    HarO gate (G g ℓ a gate) (Whir.roundsP Whir.chalE2 g ℓ) (layRounds g ℓ a) RndsRep

/-- **CC-3, the level interface** (statement): for the code facts `L`, the verifier's values
`vals`, a position gadget and a value gadget that meet `PosOK`, `ValsAt`, the generator
`G posG valsG lev wdI lvN gO gQ a gate` re-executes `tailP L chalE2 ht wd i gO gQ vals` on
`layTail`. -/
def TailHarStmt {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m')
    (G : ((Fin (L.kq + 1) → C2) → Cell → BM (List Cell)) →
      (List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2)) →
      Level → ℕ → ℕ → ℕ → Cell → BM TailOutC) : Prop :=
  ∀ (vals : List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2) posG valsG,
    PosOK L.pos posG → (∀ c M, ValsAt c M vals valsG) →
    ∀ (ht wd i gO gQ : ℕ), gO ≤ 64 → gQ ≤ 64 → ∀ (lev : Level) (wdI lvN a : ℕ) (gate : Cell),
      HarO gate (G posG valsG lev wdI lvN a gate) (Whir.tailP L Whir.chalE2 ht wd i gO gQ vals)
        (layTail L.nh L.ko L.kq L.t lev wdI ht wd lvN gO gQ a) TailRep

/-- **CC-4, one level with a next one** (statement): `ℓ` fold rounds, then the interface, whose
value gadget may read the rounds' cells (`valsG rc` meets `ValsAt` for `vals rs` whenever the
cells `rc` represent the rounds `rs`). -/
def LevelHarStmt {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m')
    (G : ((Fin (L.kq + 1) → C2) → Cell → BM (List Cell)) →
      (List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2)) →
      ℕ → ℕ → Level → ℕ → ℕ → ℕ → Cell → BM (List RndC × TailOutC)) : Prop :=
  ∀ (vals : List (Whir.Rnd E2) → List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2)
    posG valsG, PosOK L.pos posG →
    (∀ c M rc rs, RndsRep M rc rs → ValsAt c M (vals rs) (valsG rc)) →
    ∀ (g ht wd i gO gQ ℓ : ℕ), g ≤ 64 → gO ≤ 64 → gQ ≤ 64 →
    ∀ (lev : Level) (wdI lvN a : ℕ) (gate : Cell),
      HarO gate (G posG valsG g ℓ lev wdI lvN a gate)
        (Whir.levelP Whir.chalE2 L g gO gQ ht wd i ℓ vals)
        (layRounds g ℓ a ++ layTail L.nh L.ko L.kq L.t lev wdI ht wd lvN gO gQ (a + 27 * ℓ))
        LevelRep

/-- **CC-5, the ring group** (statement): `G g a gate` re-executes RS's `ringProg g`. -/
def RingHarStmt (G : ℕ → ℕ → Cell → BM RingC) : Prop :=
  ∀ g, g ≤ 64 → ∀ (a : ℕ) (gate : Cell),
    HarO gate (G g a gate) (Ring.ringProg g) (layRing g a) RingRep

/-- **CC-5′, the ring phase of `prog6`** (statement; replaces CC-5 in the node): for the static
condition `ringOK` and at most `J₀` claims, `G g svT svS vs a gate` re-executes ASM's
`ringPhase6 sh sl st` on `layRing6`, whenever the cells `svT`, `svS` hold the two slice claims' values
and `vs` the stack claims' values. -/
def RingPhaseHarStmt (G : ℕ → List C2 → List C2 → List C2 → ℕ → Cell → BM RingPhC) : Prop :=
  ∀ (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6), ringOK sh sl →
    st.length + 2 ≤ sh.J₀ → ∀ (svT svS vs : List C2) (a : ℕ) (gate : Cell),
      HarO gate (G sh.gRing svT svS vs a gate) (ringPhase6 sh sl st) (layRing6 sh.gRing a)
        fun M o out ↦ sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
          st.map (·.2) = vs.map (ev2 M) → RingPhRep sl st M o out

/-- **CC-6, the batched claim's value** (statement, FORMAT6 §6.5): from the cells of the slice
values `sv`, the ring maps `f`, `g`, `λ₀` and the values `vs` of the other stack claims, with at
most `J₀` claims in all (`V_S` rejects more; S's `ringSpec6` bound), the output cell is the value of
RS's `stackClaim` (`ring_target` first, then the claims, by the powers of `λ₀`). -/
def RingValStmt (G : List C2 → List C2 → List C2 → C2 → List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem) (sv f g : List C2) (lam : C2) (vs : List C2) (gate : Cell),
    gate.val M = 1 → vs.length + 1 ≤ P18.J₀ →
    HsA c M (G sv f g lam vs gate) fun o ↦ ∀ (μ : ℕ) (r off : List E2) (cs : List Ring.Claim),
      cs.map (·.2) = vs.map (ev2 M) →
        ev2 M o = (Ring.stackClaim μ r (sv.map (ev2 M)) off cs
          (f.map (ev2 M), g.map (ev2 M), ev2 M lam)).2

/-- **CC-6a, `ring_target`** (statement): the output cell is `ring_target(s, f, g)` at `GEN`. With
CC-6b it builds the batch in whatever order the schedule lays the claims (FORMAT6 §6.5 puts the OOD
claim at index 0, the tree ring claim at 1, the sponge's at 15; RS's `stackClaim`, CC-6, puts the
ring claim first). -/
def RingTargetStmt (G : List C2 → List C2 → List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem) (sv f g : List C2) (gate : Cell), gate.val M = 1 →
    HsA c M (G sv f g gate) fun o ↦
      ev2 M o = Ring.ringTarget Ring.genE2 (sv.map (ev2 M)) (f.map (ev2 M)) (g.map (ev2 M))

/-- **CC-6b, the batch of claim values** (statement): at most `J₀` values, the output cell is
`Σ_k λ^k v_k` (`verify_stacked_opening`'s `dotF (powers(λ, n)) v`). -/
def BatchValStmt (G : C2 → List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem) (lam : C2) (vs : List C2) (gate : Cell), gate.val M = 1 →
    vs.length ≤ P18.J₀ →
    HsA c M (G lam vs gate) fun o ↦ ev2 M o = dotF (powersF (ev2 M lam) vs.length) (vs.map (ev2 M))

/-- **CC-7, the ring claim's weight at a point** (statement): `ring_weight(r, r', c(f, g))`. -/
def RingWeightStmt (G : List C2 → List C2 → List C2 → List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem) (r r' f g : List C2) (gate : Cell), gate.val M = 1 →
    HsA c M (G r r' f g gate) fun o ↦
      ev2 M o = Ring.ringWeight (r.map (ev2 M)) (r'.map (ev2 M))
        (Ring.ringCoefficients (f.map (ev2 M)) (g.map (ev2 M)))

end Lvm6.QC
