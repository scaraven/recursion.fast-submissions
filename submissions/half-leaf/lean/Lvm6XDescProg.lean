-- lvm6 X6b/X7a (X5 §1 `DescOk6`, X4 §6 items 1–2, F-X6b-4): the descent as an XIR program whose rounds and lanes
-- are loops: per level a transition and groups of rounds, per group one `loopK` over its rounds (builder, `lamIR`,
-- one `loopK` over the lanes: loader, `laneIR`, a copy addressed by the lane register); `DescOk6` from per-part
-- budgets (`descOk6_descX6`) and the program size `≤ 2^19` (`sizeIR_descX6_le`). X7a rewrote X6b's unrolled rounds.
import Lvm6XDescIR
import Lvm6XTop

/-!
# The descent program `descX6`

* **Loop registers** `248 … 255` (above every register `lamIR`/`laneIR` (`< 208`), the copy (`64 … 69`) and the
  parts (`AllBelow rRd`) write): `rRd` the level's round index, `rLn` the lane index, `rDs` the copy's destination
  `colB + str·q`, `rSt` the stride; `cRd`/`nRd`, `cLn`/`nLn` the counters.
* **`laneX`** `= ld ; laneIR ; cpyX` (`cpyX`: `2^ℓ` words from `outA` to `M[rDs]`, then `rDs += str`, `rLn += 1`).
  **`roundL g`** `= g.sb ; lamIR ; rLn, rDs, rSt := 0, colB, str ; loopK g.n laneX ; rRd += 1`.
  **`groupX g`** `= loopK g.nr (roundL g)`: `g.nr` rounds of `g.n` lanes with one builder `g.sb` and one loader
  `g.ld`, which read the round and lane from `rRd`, `rLn` (`Lvm6XDescLoop`: their `SbOk`/`LoadOkB` per round/lane).
* **`levelX i L`** `= L.tr ; rRd := 0 ; groupX` over `L.gs`; **`descX6 L fin`** `= levelX 4 ; … ; levelX 0 ; fin`.
  Level 0 needs six groups (its rounds have 6, 64, 32, 16, 8, 4 `K`-lanes: one uniform group would charge
  `6·64` lanes, `2^43.7` steps over `descCost6`); levels 1–4 one group of four rounds of `64` lanes.
* **`descOk6_descX6`**: `DescOk6 (descX6 L fin)` when every part is well formed, has no `loopT` and no output, is
  within its budget (the builder's `sbCap i n = 2^27 + n·2^(ht6 i + 13)` affine in the round's lanes, X9), the loop
  parts write no register from `rRd` on, and each level has at most `rds i` rounds and
  `lns i` lanes in all (`LevelOk`). **`sizeIR_descX6_le`**: `sizeIR (descX6 L fin) ≤ 2^19` (X6a's `size_extX6`) when
  level 0 has at most six groups, levels 1–4 one, and the parts are within `sbSz = 2^14`, `ldSz = trSz = finSz = 2^13`
  statements (`LevelSz`): `lamIR ≤ 16,064`, `laneIR ≤ 1,617` statements at every level.
* X4's unrolled round `roundX` (`RoundX`, `roundX_sem`) is kept: X6b's `roundX_semB` and the size finding use it.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-! ## The program -/

/-- The agreement-set builder's budget for a round of `n` lanes at level `i` (affine: X8a F-X8a-1). -/
def sbCap (i n : ℕ) : ℕ := 2 ^ 27 + n * 2 ^ (ht6 i + 13)
/-- A lane loader's budget. -/ def ldCap : ℕ := 2 ^ 26
/-- A level transition's budget. -/ def trCap : ℕ := 2 ^ 38
/-- The level-0 map's budget. -/ def finCap : ℕ := 2 ^ 38

/-- **One decoded round**: the builder `sb` of `S` (`|S| = m`), the loaders `ld`, `n` lanes. -/
structure RoundX where
  sb : XIR
  ld : ℕ → XIR
  n : ℕ
  m : ℕ

/-- The round on the machine. -/
def roundX (N ℓ B colB str : ℕ) (r : RoundX) : XIR := .seq r.sb (roundIR N ℓ r.m B colB str r.ld r.n)


/-! ## The loops (F-X6b-4) -/

/-- The round index (level-wide, from `0`). -/ def rRd : ℕ := 248
/-- The lane index (from `0`). -/ def rLn : ℕ := 249
/-- The copy's destination `colB + str·q`. -/ def rDs : ℕ := 250
/-- The stride. -/ def rSt : ℕ := 251
/-- The round counter. -/ def cRd : ℕ := 252
/-- Its count. -/ def nRd : ℕ := 253
/-- The lane counter. -/ def cLn : ℕ := 254
/-- Its count. -/ def nLn : ℕ := 255

/-- **The copy addressed by the lane register**: `2^ℓ` words from `outA B ℓ` to `M[rDs]`, then `rDs += rSt`,
`rLn += 1`. -/
def cpyX (ℓ B : ℕ) : XIR :=
  .seq (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs])
    (.seq (mcpLoop (2 ^ ℓ)) (.blk [.op .add rDs rDs rSt, .op .add rLn rLn cOne]))

/-- **One lane**: the loader, `laneIR`, the copy. -/
def laneX (N ℓ m B : ℕ) (ld : XIR) : XIR := .seq ld (.seq (laneIR N ℓ m B) (cpyX ℓ B))

/-- **A group of rounds**: `nr` rounds of `n` lanes, `|S| = m`, one builder `sb` and one loader `ld` (they read the
round and the lane from `rRd`, `rLn`). -/
structure GroupX where
  sb : XIR
  ld : XIR
  nr : ℕ
  n : ℕ
  m : ℕ

/-- The lanes of a round, a loop. -/
def lanesX (N ℓ m B : ℕ) (ld : XIR) (n : ℕ) : XIR := .loopK cLn nLn (toWord n) (laneX N ℓ m B ld)

/-- **One round**: the builder, `Λ`, the lane registers, the lanes, the next round index. -/
def roundL (N ℓ B colB str : ℕ) (g : GroupX) : XIR :=
  .seq g.sb (.seq (lamIR N ℓ g.m B) (.seq (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
    .const nLn (toWord g.n)]) (.seq (lanesX N ℓ g.m B g.ld g.n) (.blk [.op .add rRd rRd cOne]))))

/-- **The rounds of a group**, a loop. -/
def groupX (N ℓ B colB str : ℕ) (g : GroupX) : XIR :=
  .seq (.blk [.const nRd (toWord g.nr)]) (.loopK cRd nRd (toWord g.nr) (roundL N ℓ B colB str g))

/-- A level's groups, in order. -/
def groupsX (N ℓ B colB str : ℕ) : List GroupX → XIR
  | [] => .blk []
  | g :: gs => .seq (groupX N ℓ B colB str g) (groupsX N ℓ B colB str gs)

/-- **One level**: the transition `tr`, then the groups of rounds (last round first), in the scratch `B` with the
copies at `colB + str·q`. -/
structure LevelX where
  tr : XIR
  gs : List GroupX
  B : ℕ
  colB : ℕ
  str : ℕ

/-- Level `i` on the machine (domain `2^ht6 i`, table dimension `ht6 i + 1`); the round index starts at `0`. -/
def levelX (i : ℕ) (L : LevelX) : XIR :=
  .seq L.tr (.seq (.blk [.const rRd 0]) (groupsX (ht6 i + 1) (ht6 i) L.B L.colB L.str L.gs))

/-- **The descent**: levels 4 down to 0, then the level-0 map `fin`. -/
def descX6 (L : ℕ → LevelX) (fin : XIR) : XIR :=
  .seq (levelX 4 (L 4)) (.seq (levelX 3 (L 3)) (.seq (levelX 2 (L 2)) (.seq (levelX 1 (L 1))
    (.seq (levelX 0 (L 0)) fin))))

/-! ## The parts' obligations -/

/-- A part: well formed, no `loopT`, no output, within `c` steps. -/
structure PartOk (P : XIR) (c : ℕ) : Prop where
  wf : WF P
  noLoopT : NoLoopT P
  outs : ∀ t, outs P t = 0
  cost : ∀ t, cost P t ≤ c

/-- A part inside the loops: also no register from `rRd` on as a destination. -/
structure LoopPart (P : XIR) (c : ℕ) : Prop extends PartOk P c where
  low : AllBelow rRd P

/-- A group of level `i`: builder and loader within budget, `|S|` within the domain, at most `lns i` lanes a round. -/
structure GroupOk (i : ℕ) (g : GroupX) : Prop where
  sb : LoopPart g.sb (sbCap i g.n)
  ld : LoopPart g.ld ldCap
  m : g.m ≤ 2 ^ ht6 i
  n : g.n ≤ lns i

/-- Level `i`: transition within budget, every group ok, at most `rds i` groups and rounds, `lns i` lanes. -/
structure LevelOk (i : ℕ) (L : LevelX) : Prop where
  tr : PartOk L.tr trCap
  gs : ∀ g ∈ L.gs, GroupOk i g
  len : L.gs.length ≤ rds i
  rounds : (L.gs.map GroupX.nr).sum ≤ rds i
  lanes : (L.gs.map fun g ↦ g.nr * g.n).sum ≤ lns i

/-! ## Structure -/

theorem nw_cpyX (ℓ B : ℕ) {r : ℕ} (hr : rRd ≤ r) (h1 : r ≠ rDs) (h2 : r ≠ rLn) : ¬ Writes (cpyX ℓ B) r := by
  intro h
  simp only [cpyX, mcpLoop, mcpBody, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
    exists_eq_or_imp, exists_eq_left, ySr, yStr, yDs, yN, yC, yV, cTmp, rDs, rLn, rRd, rSt] at h hr h1 h2
  omega

theorem wf_cpyX (ℓ B : ℕ) : WF (cpyX ℓ B) := by
  simp +decide [cpyX, mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yStr, yV, yC, yN, rDs, rLn, rSt]

theorem noLoopT_cpyX (ℓ B : ℕ) : NoLoopT (cpyX ℓ B) := by simp [cpyX, mcpLoop, mcpBody, NoLoopT]

theorem outs_cpyX (ℓ B t : ℕ) : outs (cpyX ℓ B) t = 0 := by simp [cpyX, mcpLoop, mcpBody, outs]

theorem wf_laneX {N ℓ m B : ℕ} {ld : XIR} (hw : WF ld) : WF (laneX N ℓ m B ld) := ⟨hw, wf_laneIR .., wf_cpyX ..⟩

theorem nw_laneX {N ℓ m B : ℕ} {ld : XIR} (hl : AllBelow rRd ld) {r : ℕ} (hr : rRd ≤ r) (h1 : r ≠ rDs)
    (h2 : r ≠ rLn) : ¬ Writes (laneX N ℓ m B ld) r :=
  nw_seq (nw_of_allBelow hr hl) (nw_seq (nw_laneIR _ _ _ _ (by simp only [rRd] at hr; omega)) (nw_cpyX ℓ B hr h1 h2))

theorem nw_roundL_cRd {N ℓ B colB str : ℕ} {g : GroupX} (hs : AllBelow rRd g.sb) (hl : AllBelow rRd g.ld) :
    ¬ Writes (roundL N ℓ B colB str g) cRd :=
  nw_seq (nw_of_allBelow (by decide) hs) (nw_seq (nw_lamIR _ _ _ _ (by decide))
    (nw_seq (nw_blk (by simp +decide [Prim.dst, rLn, rDs, rSt, nLn, cRd]))
      (nw_seq (nw_loopK (by decide) (by decide) (nw_laneX hl (by decide) (by decide) (by decide)))
        (nw_blk (by simp +decide)))))

theorem wf_roundL {N ℓ B colB str : ℕ} {g : GroupX} (hs : WF g.sb) (hl : WF g.ld) (hla : AllBelow rRd g.ld) :
    WF (roundL N ℓ B colB str g) :=
  ⟨hs, wf_lamIR .., by simp +decide [WF, Prim.dst, rLn, rDs, rSt, nLn],
    ⟨⟨by decide, by decide, by decide⟩, by decide, nw_laneX hla (by decide) (by decide) (by decide), wf_laneX hl⟩,
    by simp +decide [WF]⟩

theorem groupX_struct {N ℓ B colB str : ℕ} {g : GroupX} {c c' : ℕ} (hs : LoopPart g.sb c) (hl : LoopPart g.ld c') :
    WF (groupX N ℓ B colB str g) ∧ NoLoopT (groupX N ℓ B colB str g) ∧
      ∀ t, outs (groupX N ℓ B colB str g) t = 0 := by
  refine ⟨⟨by simp +decide [WF, Prim.dst, nRd], ⟨by decide, by decide, by decide⟩, by decide,
    nw_roundL_cRd hs.low hl.low, wf_roundL hs.wf hl.wf hl.low⟩,
    ⟨trivial, hs.noLoopT, noLoopT_lamIR .., trivial, ⟨hl.noLoopT, noLoopT_laneIR .., noLoopT_cpyX ..⟩, trivial⟩,
    fun t ↦ ?_⟩
  simp only [groupX, roundL, lanesX, laneX, outs, hs.outs, hl.outs, outs_lamIR, outs_laneIR, outs_cpyX,
    Nat.add_zero, Nat.mul_zero]

theorem groupsX_struct (i B colB str : ℕ) : ∀ gs : List GroupX, (∀ g ∈ gs, GroupOk i g) →
    WF (groupsX (ht6 i + 1) (ht6 i) B colB str gs) ∧ NoLoopT (groupsX (ht6 i + 1) (ht6 i) B colB str gs) ∧
      ∀ t, outs (groupsX (ht6 i + 1) (ht6 i) B colB str gs) t = 0
  | [], _ => ⟨by simp [groupsX, WF], by simp [groupsX, NoLoopT], fun _ ↦ by simp [groupsX, outs]⟩
  | g :: gs, h => by
    have hg := h g List.mem_cons_self
    obtain ⟨a, b, c⟩ := groupX_struct (N := ht6 i + 1) (ℓ := ht6 i) (B := B) (colB := colB) (str := str) hg.sb hg.ld
    obtain ⟨a', b', c'⟩ := groupsX_struct i B colB str gs fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg')
    exact ⟨⟨a, a'⟩, ⟨b, b'⟩, fun t ↦ by simp only [groupsX, outs, c, c', Nat.add_zero]⟩

theorem levelX_struct {i : ℕ} {L : LevelX} (h : LevelOk i L) :
    WF (levelX i L) ∧ NoLoopT (levelX i L) ∧ ∀ t, outs (levelX i L) t = 0 := by
  obtain ⟨a, b, c⟩ := groupsX_struct i L.B L.colB L.str L.gs h.gs
  exact ⟨⟨h.tr.wf, by simp +decide [WF], a⟩, ⟨h.tr.noLoopT, trivial, b⟩,
    fun t ↦ by simp only [levelX, outs, h.tr.outs, c, Nat.add_zero]⟩

/-! ## Cost -/

theorem cost_cpyX (ℓ B t : ℕ) (hℓ : 2 ^ ℓ < 2 ^ 64) : cost (cpyX ℓ B) t = 20 + 13 * 2 ^ ℓ := by
  simp only [cpyX, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hℓ]
  norm_num
  try ring

theorem cost_laneX (N ℓ m B t : ℕ) (ld : XIR) (hN : ℓ + 1 ≤ N) (hN63 : N ≤ 63) (hm : m < 2 ^ 64)
    (hℓ : 2 ^ ℓ < 2 ^ 64) : cost (laneX N ℓ m B ld) t = cost ld t + laneCost N ℓ m + 22 + 13 * 2 ^ ℓ := by
  simp only [laneX, cost, (fd1_cost N ℓ m B t hN hN63 hm).2, cost_cpyX ℓ B t hℓ]
  ring

theorem cost_roundL (N ℓ B colB str t : ℕ) (g : GroupX) (hN : ℓ + 1 ≤ N) (hN63 : N ≤ 63) (hm : g.m < 2 ^ 64)
    (hℓ : 2 ^ ℓ < 2 ^ 64) (hn : g.n < 2 ^ 64) : cost (roundL N ℓ B colB str g) t =
      cost g.sb t + lamCost N ℓ g.m + 20 + g.n * (cost g.ld t + laneCost N ℓ g.m + 25 + 13 * 2 ^ ℓ) := by
  simp only [roundL, lanesX, cost, (fd1_cost N ℓ g.m B t hN hN63 hm).1, cost_laneX N ℓ g.m B t g.ld hN hN63 hm hℓ,
    blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num
  ring

theorem cost_groupX (N ℓ B colB str t : ℕ) (g : GroupX) (hnr : g.nr < 2 ^ 64) :
    cost (groupX N ℓ B colB str g) t = 10 + g.nr * (cost (roundL N ℓ B colB str g) t + 3) := by
  simp only [groupX, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hnr]
  norm_num
  ring

/-- A group's cost at level `i`: per round the builder and `Λ`, per lane the loader, `laneIR` and the copy. -/
theorem cost_groupX_le {i B colB str : ℕ} {g : GroupX} (h : GroupOk i g) (hnr : g.nr ≤ rds i) (t : ℕ) :
    cost (groupX (ht6 i + 1) (ht6 i) B colB str g) t ≤
      g.nr * (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
        g.nr * g.n * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i +
          2 ^ (ht6 i + 13)) + 10 := by
  have h21 := ht6_le i
  have hp : 2 ^ ht6 i ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) h21
  have hr6 : rds i ≤ 6 := by unfold rds; split <;> omega
  have hl6 : lns i ≤ 256 := by unfold lns; split <;> omega
  have hn := h.n
  have hmm := h.m
  rw [cost_groupX _ _ _ _ _ t g (by omega), cost_roundL _ _ _ _ _ t g le_rfl (by omega) (by omega) (by omega)
    (by omega)]
  have hX : cost g.ld t + laneCost (ht6 i + 1) (ht6 i) g.m + 25 + 13 * 2 ^ ht6 i ≤
      laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i := by
    have := h.ld.cost t; have := laneCost_mono (N := ht6 i + 1) (ℓ := ht6 i) h.m; omega
  have hR : cost g.sb t + lamCost (ht6 i + 1) (ht6 i) g.m + 20 +
      g.n * (cost g.ld t + laneCost (ht6 i + 1) (ht6 i) g.m + 25 + 13 * 2 ^ ht6 i) + 3 ≤
      (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
        g.n * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13)) := by
    have := Nat.mul_le_mul_left g.n hX; have := h.sb.cost t
    have := Nat.mul_add g.n (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i)
      (2 ^ (ht6 i + 13))
    have := lamCost_mono (N := ht6 i + 1) (ℓ := ht6 i) h.m; simp only [sbCap] at *; omega
  calc 10 + g.nr * (cost g.sb t + lamCost (ht6 i + 1) (ht6 i) g.m + 20 +
        g.n * (cost g.ld t + laneCost (ht6 i + 1) (ht6 i) g.m + 25 + 13 * 2 ^ ht6 i) + 3)
      ≤ 10 + g.nr * ((lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
        g.n * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13))) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hR) _
    _ = _ := by ring

/-- A level's groups. -/
theorem cost_groupsX_le (i B colB str t : ℕ) : ∀ gs : List GroupX, (∀ g ∈ gs, GroupOk i g ∧ g.nr ≤ rds i) →
    cost (groupsX (ht6 i + 1) (ht6 i) B colB str gs) t ≤
      (gs.map GroupX.nr).sum * (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
        (gs.map fun g ↦ g.nr * g.n).sum * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 +
          13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13)) +
          11 * gs.length + 1
  | [], _ => by simp [groupsX, cost, blkSteps]
  | g :: gs, h => by
    have h1 := cost_groupX_le (B := B) (colB := colB) (str := str) (h g List.mem_cons_self).1
      (h g List.mem_cons_self).2 t
    have h2 := cost_groupsX_le i B colB str t gs fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg')
    simp only [groupsX, cost, List.length_cons, List.map_cons, List.sum_cons]
    nlinarith

/-- The part of level `i` outside the decoder. -/
def exL (i : ℕ) : ℕ :=
  trCap + rds i * (2 ^ 27 + 34) + lns i * (ldCap + 25 + 13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13)) + 4

theorem cost_levelX_le {i : ℕ} {L : LevelX} (h : LevelOk i L) (t : ℕ) :
    cost (levelX i L) t ≤ descLvl i (2 ^ ht6 i) + exL i := by
  have hnr : ∀ g ∈ L.gs, g.nr ≤ rds i := fun g hg ↦ le_trans
    (List.le_sum_of_mem (List.mem_map_of_mem (f := GroupX.nr) hg)) h.rounds
  have h1 := cost_groupsX_le i L.B L.colB L.str t L.gs fun g hg ↦ ⟨h.gs g hg, hnr g hg⟩
  have h2 := Nat.mul_le_mul_right (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) h.rounds
  have h3 := Nat.mul_le_mul_right (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i +
    2 ^ (ht6 i + 13)) h.lanes
  have h4 := h.tr.cost t
  have h5 := h.len
  have e : cost (.blk [.const rRd 0]) t = 1 := rfl
  simp only [levelX, cost] at e ⊢
  simp only [descLvl, exL]
  nlinarith

/-- **The parts outside the decoder fit `2^43`.** -/
theorem exL_sum_le : exL 0 + exL 1 + exL 2 + exL 3 + exL 4 + finCap + 5 ≤ 2 ^ 43 := by
  simp only [exL, rds, lns, ht6, trCap, ldCap, finCap]
  norm_num

/-- **`DescOk6` of the concrete descent**, from its parts' obligations. -/
theorem descOk6_descX6 {L : ℕ → LevelX} {fin : XIR} (hL : ∀ i < 5, LevelOk i (L i)) (hf : PartOk fin finCap) :
    DescOk6 (descX6 L fin) := by
  obtain ⟨w4, n4, o4⟩ := levelX_struct (hL 4 (by norm_num))
  obtain ⟨w3, n3, o3⟩ := levelX_struct (hL 3 (by norm_num))
  obtain ⟨w2, n2, o2⟩ := levelX_struct (hL 2 (by norm_num))
  obtain ⟨w1, n1, o1⟩ := levelX_struct (hL 1 (by norm_num))
  obtain ⟨w0, n0, o0⟩ := levelX_struct (hL 0 (by norm_num))
  refine ⟨⟨w4, w3, w2, w1, w0, hf.wf⟩, ⟨n4, n3, n2, n1, n0, hf.noLoopT⟩, fun t ↦ ?_, fun t ↦ ?_⟩
  · simp only [descX6, outs, o4, o3, o2, o1, o0, hf.outs]
  · have c4 := cost_levelX_le (hL 4 (by norm_num)) t
    have c3 := cost_levelX_le (hL 3 (by norm_num)) t
    have c2 := cost_levelX_le (hL 2 (by norm_num)) t
    have c1 := cost_levelX_le (hL 1 (by norm_num)) t
    have c0 := cost_levelX_le (hL 0 (by norm_num)) t
    have cf := hf.cost t
    have hs := exL_sum_le
    simp only [descX6, cost, descCost6]
    omega

/-- **T8 `computes6` for the concrete descent** (X5's `computes6` at `descX6 L fin`). -/
theorem computes6_descX6 {L : ℕ → LevelX} {fin : XIR} (hL : ∀ i < 5, LevelOk i (L i))
    (hf : PartOk fin finCap) : Stmt.computes6 (extX6 (descX6 L fin)) (EX6 (descX6 L fin)) :=
  computes6 (descOk6_descX6 hL hf)

/-! ## Program size: `sizeIR descX6 ≤ 2^19` -/

/-- The builder's size cap. -/ def sbSz : ℕ := 2 ^ 14
/-- The loader's size cap. -/ def ldSz : ℕ := 2 ^ 13
/-- The transition's size cap. -/ def trSz : ℕ := 2 ^ 13
/-- The level-0 map's size cap. -/ def finSz : ℕ := 2 ^ 13
/-- Groups a level: six at level 0 (one a round), one at levels 1–4. -/
def gCap : ℕ → ℕ
  | 0 => 6
  | _ => 1

/-- Level `i`'s parts within their size caps. -/
structure LevelSz (i : ℕ) (L : LevelX) : Prop where
  tr : sizeIR L.tr ≤ trSz
  sb : ∀ g ∈ L.gs, sizeIR g.sb ≤ sbSz
  ld : ∀ g ∈ L.gs, sizeIR g.ld ≤ ldSz
  len : L.gs.length ≤ gCap i

theorem sizeIR_cpyX (ℓ B : ℕ) : sizeIR (cpyX ℓ B) = 34 := rfl

theorem sizeIR_groupX (N ℓ B colB str : ℕ) (g : GroupX) : sizeIR (groupX N ℓ B colB str g) =
    sizeIR g.sb + sizeIR g.ld + sizeIR (lamIR N ℓ g.m B) + sizeIR (laneIR N ℓ g.m B) + 72 := by
  simp only [groupX, roundL, lanesX, laneX, sizeIR, sizeIR_cpyX, blkSteps, List.length_cons, List.length_nil]
  norm_num
  omega

/-- `lamIR`'s size does not depend on `|S|` or the scratch base. -/
theorem sizeIR_lamIR_free (N ℓ m B : ℕ) : sizeIR (lamIR N ℓ m B) = sizeIR (lamIR N ℓ 0 0) := by
  have ht : ∀ h, sizeIR (treeIR N ℓ B h) = sizeIR (treeIR N ℓ 0 h) := by
    intro h
    induction h with
    | zero => rfl
    | succ h ih =>
      simp only [treeIR, tLevelIR, parentBody, sizeIR, bflyNIR, fwdNIR, ih, List.length_cons, List.length_nil]
  simp only [lamIR, sizeIR, leavesIR, dummiesIR, dummyBody, invsIR, wtabNIR, ht, List.length_cons, List.length_nil]

/-- `lamIR`'s statements at every level (`treeIR` unrolls its `ℓ` tree levels): 15,409, 14,754, 14,099, 13,444,
12,789 at `P17` (kernel evaluation; the cap 16,064 is `P18`'s level 0). -/
theorem sizeIR_lamIR_le (i m B : ℕ) : sizeIR (lamIR (ht6 i + 1) (ht6 i) m B) ≤ 16064 := by
  have e0 : sizeIR (lamIR 21 20 0 0) = 15409 := by decide +kernel
  have e1 : sizeIR (lamIR 20 19 0 0) = 14754 := by decide +kernel
  have e2 : sizeIR (lamIR 19 18 0 0) = 14099 := by decide +kernel
  have e3 : sizeIR (lamIR 18 17 0 0) = 13444 := by decide +kernel
  have e4 : sizeIR (lamIR 17 16 0 0) = 12789 := by decide +kernel
  rw [sizeIR_lamIR_free]
  rcases i with _ | _ | _ | _ | i
  · exact e0.le.trans (by norm_num)
  · exact e1.le.trans (by norm_num)
  · exact e2.le.trans (by norm_num)
  · exact e3.le.trans (by norm_num)
  · exact e4.le.trans (by norm_num)

/-- `laneIR`'s size does not depend on `|S|` or the scratch base. -/
theorem sizeIR_laneIR_free (N ℓ m B : ℕ) : sizeIR (laneIR N ℓ m B) = sizeIR (laneIR N ℓ 0 0) := by
  simp only [laneIR, sizeIR, zeroGIR, synIR, synBody, corrIR, cosIR, bflyNIR, fwdNIR, List.length_cons,
    List.length_nil]

/-- `laneIR`'s statements at every level: 1,617 (kernel evaluation). -/
theorem sizeIR_laneIR_le (i m B : ℕ) : sizeIR (laneIR (ht6 i + 1) (ht6 i) m B) ≤ 1617 := by
  have e0 : sizeIR (laneIR 21 20 0 0) = 1617 := by decide +kernel
  have e1 : sizeIR (laneIR 20 19 0 0) = 1617 := by decide +kernel
  have e2 : sizeIR (laneIR 19 18 0 0) = 1617 := by decide +kernel
  have e3 : sizeIR (laneIR 18 17 0 0) = 1617 := by decide +kernel
  have e4 : sizeIR (laneIR 17 16 0 0) = 1617 := by decide +kernel
  rw [sizeIR_laneIR_free]
  rcases i with _ | _ | _ | _ | i
  · exact e0.le
  · exact e1.le
  · exact e2.le
  · exact e3.le
  · exact e4.le

theorem sizeIR_groupsX_le (i B colB str : ℕ) : ∀ gs : List GroupX,
    (∀ g ∈ gs, sizeIR g.sb ≤ sbSz ∧ sizeIR g.ld ≤ ldSz) →
    sizeIR (groupsX (ht6 i + 1) (ht6 i) B colB str gs) ≤ gs.length * 42330 + 1
  | [], _ => by simp [groupsX, sizeIR, blkSteps]
  | g :: gs, h => by
    have hg := h g List.mem_cons_self
    have h1 := sizeIR_groupsX_le i B colB str gs fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg')
    have h2 := sizeIR_lamIR_le i g.m B
    have h3 := sizeIR_laneIR_le i g.m B
    have e : sizeIR (groupsX (ht6 i + 1) (ht6 i) B colB str (g :: gs)) =
        sizeIR (groupX (ht6 i + 1) (ht6 i) B colB str g) + sizeIR (groupsX (ht6 i + 1) (ht6 i) B colB str gs) + 1 :=
      rfl
    rw [e, sizeIR_groupX, List.length_cons]
    simp only [sbSz, ldSz] at hg
    omega

theorem sizeIR_levelX_le {i : ℕ} {L : LevelX} (h : LevelSz i L) :
    sizeIR (levelX i L) ≤ trSz + gCap i * 42330 + 4 := by
  have h1 := sizeIR_groupsX_le i L.B L.colB L.str L.gs fun g hg ↦ ⟨h.sb g hg, h.ld g hg⟩
  have h2 := Nat.mul_le_mul_right 42330 h.len
  have e : sizeIR (levelX i L) = sizeIR L.tr + (1 + sizeIR (groupsX (ht6 i + 1) (ht6 i) L.B L.colB L.str L.gs) + 1)
    + 1 := rfl
  have := h.tr
  omega

/-- **The descent fits `2^19` statements** (X6a's `size_extX6`): `≤ 472,477`. -/
theorem sizeIR_descX6_le {L : ℕ → LevelX} {fin : XIR} (hS : ∀ i < 5, LevelSz i (L i)) (hf : sizeIR fin ≤ finSz) :
    sizeIR (descX6 L fin) ≤ 2 ^ 19 := by
  have h4 := sizeIR_levelX_le (hS 4 (by norm_num))
  have h3 := sizeIR_levelX_le (hS 3 (by norm_num))
  have h2 := sizeIR_levelX_le (hS 2 (by norm_num))
  have h1 := sizeIR_levelX_le (hS 1 (by norm_num))
  have h0 := sizeIR_levelX_le (hS 0 (by norm_num))
  simp only [gCap, trSz] at h4 h3 h2 h1 h0
  simp only [finSz] at hf
  simp only [descX6, sizeIR]
  omega

/-! ## X4's unrolled lanes (F-X6b-4: why the loops above) -/

/-- X4's lanes are unrolled: every lane carries its own copy of `laneIR`. -/
theorem le_sizeIR_lanesIR (N ℓ m B colB str : ℕ) (ld : ℕ → XIR) (n : ℕ) :
    ∀ l, n * sizeIR (laneIR N ℓ m B) ≤ sizeIR (lanesIR N ℓ m B colB str ld n l) := by
  induction n with
  | zero => intro l; rw [Nat.zero_mul]; exact Nat.zero_le _
  | succ n ih =>
    intro l
    have h := ih (l + 1)
    have e : sizeIR (lanesIR N ℓ m B colB str ld (n + 1) l) = sizeIR (ld l) + (sizeIR (laneIR N ℓ m B) +
        (sizeIR (mcpIR (2 ^ ℓ) (outA B ℓ) 1 (colB + str * l)) + sizeIR (lanesIR N ℓ m B colB str ld n (l + 1)) + 1)
          + 1) + 1 := by
      rw [lanesIR]; rfl
    rw [e, Nat.succ_mul]
    omega

/-- **A round's size grows with its lanes**: `n · sizeIR laneIR ≤ sizeIR (roundX r)`. With `sizeIR laneIR = 1,617`
at every level (evaluated) and the `1,154` lanes `descCost6` counts, `descX6` built from X4's `roundIR` has more than
`1.8·10^6 > 2^19` statements: the lanes (and `lamIR`, 16,064 statements, once per round) must become loops. -/
theorem le_sizeIR_roundX (N ℓ B colB str : ℕ) (r : RoundX) :
    r.n * sizeIR (laneIR N ℓ r.m B) ≤ sizeIR (roundX N ℓ B colB str r) := by
  have h := le_sizeIR_lanesIR N ℓ r.m B colB str r.ld r.n 0
  have e : sizeIR (roundX N ℓ B colB str r) = sizeIR r.sb + (sizeIR (lamIR N ℓ r.m B) +
      sizeIR (lanesIR N ℓ r.m B colB str r.ld r.n 0) + 1) + 1 := rfl
  omega

/-! ## A round's semantics -/

/-- **The agreement-set builder**: from a state satisfying `Pre`, it writes `S` at `sA B` and no other heap word
below `yA B ℓ` or from it; keeps `Inv` and the output. -/
def SbOk (I : Array Word) (sb : XIR) (B : ℕ) (S : List ℕ) (Pre : St → Prop) : Prop :=
  ∀ s : St, Pre s → Inv s.M → (∀ i < S.length, rd (semXIR I sb s).M (sA B + i) = toWord (S.getD i 0)) ∧
    Inv (semXIR I sb s).M ∧ (semXIR I sb s).o = s.o ∧
    ∀ x, regs ≤ x → (x < sA B ∨ sA B + S.length ≤ x) → rd (semXIR I sb s).M x = rd s.M x

/-- **A round on the machine**: after the builder, X4's `roundIR_sem`. -/
theorem roundX_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str : ℕ} {r : RoundX} {S : List ℕ}
    {Pre : St → Prop} (hP : Pre s) (hsb : SbOk I r.sb B S Pre) (hmS : S.length = r.m) (ys : ℕ → ℕ → BF64)
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * r.n < 2 ^ 64)
    (hsz : colB + str * r.n ≤ s.M.size) (hld : ∀ q < r.n, LoadOk I (r.ld q) ℓ B (ys q)) :
    (∀ q < r.n, ∀ x < 2 ^ ℓ, rdK (semXIR I (roundX N ℓ B colB str r) s).M (colB + str * q + x) =
        fd1 N ℓ S (ys q) x) ∧
      Inv (semXIR I (roundX N ℓ B colB str r) s).M ∧ (semXIR I (roundX N ℓ B colB str r) s).o = s.o ∧
      ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * r.n ≤ x) →
        rd (semXIR I (roundX N ℓ B colB str r) s).M x = rd s.M x := by
  obtain ⟨a1, a2, a3, a4⟩ := hsb s hP hM
  have z1 := size_sem I r.sb s
  rw [roundX, semXIR_seq, ← hmS]
  generalize semXIR I r.sb s = s1 at a1 a2 a3 a4 z1
  obtain ⟨b1, b2, b3, b4⟩ := roundIR_sem I s1 a2 r.ld ys hN hN64 hB hm hSn a1 hcol hstr h64 (by rw [z1]; exact hsz)
    hld
  have eS : sA B = B + 4096 := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  refine ⟨b1, b2, b3.trans a3, fun x hx hx' ↦ ?_⟩
  rw [b4 x hx (by omega), a4 x hx (by omega)]

end Lvm6.X
