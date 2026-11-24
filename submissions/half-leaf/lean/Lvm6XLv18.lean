-- lvm6 EXG (DP6 §2 item 3): the concrete descent (at `P17` heights since PORT17 X1). Per level a layout (buffers, tables, scratch, columns)
-- in the `2^30` words, the groups (level 0: six one-round groups of 4, 8, 16, 32, 64, 67 columns; levels 1–4: one
-- group of four rounds × 32 columns), the transitions with the level glue (`tr0M`, `trM`, `trF`) and `finX`
-- (`finIR`, the 34 stack slots from level 0's real columns). Proved: `GroupOk` of every group, `LevelOk` at levels
-- 1–4, `LevelSz`, `sizeIR ≤ 2^19`, **`DescOk6`** (directly: level 0's 191 columns exceed `lns 0 = 130`, so `LevelOk 0`
-- fails — `not_levelOk_0` — but the whole descent is within `descCost6 + 2^43`), the layout facts `levelX_cols`
-- and `glueIR_cols` need, and `GrpsOK` from X9's tables and the agreement fact (`grpsOK`). New.
import Lvm6XGlue

/-!
# The descent (at `P17`: heights `ht6 = 20 … 16`, `kapD = 18, 14, 10, 6, 2`)

* `kapD i`, `rndD i`, `dD i = 2^κ − 1 + ℓ`: W1's `ladD` levels at `P17` (PORT17, X1): `(κ, ℓ) = (18,6), (14,4), (10,4), (6,4), (2,4)`.
* Layout: `bfD i k` (buffer `k`, `bsz` words; levels 1–4 buffer `0` is the committed rows `wB6 i`), `tbD`, `tSD`,
  `BD`, `colBD`, `strD i = 2^ht6 i`. At `P18` level 0 (last in time) used `[2^28, 2^30)` and
  `[wB6 0 + 46·2^21, 2^28)`, levels 1–4 `[331350016, 470696192 + 32·2^17)`; at `P17` the bases are kept and every
  table and column block halves with its height.
* `gsD`, `ncD` (columns at round `r`: `2·2^r`; level 0 ends with 67 = lanes `0 … 33` real and imaginary, enough
  for the 34 stack slots), `FrontA` (the cells the front fills: challenge pairs, high parts, final scalars), `LvD`,
  `finX`.
* **`groupOk`**, **`levelOk`** (`1 ≤ i < 5`), **`not_levelOk_0`**, **`levelSz`**, **`sizeIR_desc`**,
  **`descOk6`**, **`grpsOK`**, `layoutD`, `glueLay`; `rep_start_0 … _4`: the starts are W1's
  `mid0 … mid3` candidates and `finD`'s final polynomial (`rep_cand`, `rep_fpoly`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-! ## Parameters -/

/-- Level `i`'s message variables (W1's `ladD`). -/
def kapD : ℕ → ℕ
  | 0 => 18
  | 1 => 14
  | 2 => 10
  | 3 => 6
  | _ => 2

/-- Level `i`'s fold rounds. -/
def rndD : ℕ → ℕ
  | 0 => 6
  | _ => 4

/-- Level `i`'s degree `2^κ − 1 + ℓ`. -/
def dD (i : ℕ) : ℕ := 2 ^ kapD i - 1 + rndD i

/-! ## The layout -/

/-- Buffer `k` of level `i` (`bsz (ht6 i) 0 (rndD i) k` words). -/
def bfD : ℕ → ℕ → ℕ
  | 0, k => [268435456, 536870912, 671088640, 738197504, 234881024, 251658240, 260046848].getD k 0
  | 1, k => [268435456, 331350016, 348127232, 356515840, 360710144].getD k 0
  | 2, k => [301989888, 407900224, 416288832, 420483136, 422580288].getD k 0
  | 3, k => [318767104, 446177408, 450371712, 452468864, 453517440].getD k 0
  | _, k => [327155712, 465318080, 467415232, 468463808, 468988096].getD k 0

/-- The loaders' table. -/
def tbD : ℕ → ℕ
  | 0 => 264241152
  | 1 => 362807296
  | 2 => 423628864
  | 3 => 454041728
  | _ => 469250240

/-- The builder's table. -/
def tSD (i : ℕ) : ℕ := tbD i + 16

/-- The decoder's scratch. -/
def BD : ℕ → ℕ
  | 0 => 771751936
  | 1 => 362807360
  | 2 => 423628928
  | 3 => 454041792
  | _ => 469250304

/-- The columns. -/
def colBD : ℕ → ℕ
  | 0 => 805306368
  | 1 => 374345792
  | 2 => 429400192
  | 3 => 456929472
  | _ => 470696192

/-- The column stride. -/
def strD (i : ℕ) : ℕ := 2 ^ ht6 i

/-! ## The groups -/

/-- A group of level `i`: `nr` rounds of `n` columns, the builder's lane bound `K`. -/
def grpD (i nr n K : ℕ) : GroupX :=
  ⟨sbIR (ht6 i + 1) (ht6 i) (BD i) (colBD i) (strD i) (dD i) (tSD i) K, ldF (tbD i) (BD i) (ht6 i), nr, n,
    dD i + 3⟩

/-- Level `i`'s groups. -/
def gsD : ℕ → List GroupX
  | 0 => [grpD 0 1 4 2, grpD 0 1 8 4, grpD 0 1 16 8, grpD 0 1 32 16, grpD 0 1 64 32, grpD 0 1 67 64]
  | i + 1 => [grpD (i + 1) 4 32 16]

/-- The columns at round `r` of level `i`. -/
def ncD (i r : ℕ) : ℕ := if i = 0 ∧ r = 6 then 67 else 2 * 2 ^ r

/-- **The cells the front fills**: the challenge pairs `ch i k` (W1's `(α, β)` of round `k` of level `i`, two `E2`),
the high parts `hi i` (`E2` scalar `k` at `hi i + 2k`), the final scalars `s`. -/
structure FrontA where
  ch : ℕ → ℕ → ℕ
  hi : ℕ → ℕ
  s : ℕ

/-- **The levels** (`P17`): level 0 glues level 1's columns and expands the committed rows; levels 1–3 glue the
next level's columns; level 4 starts from `s`. -/
def LvD (F : FrontA) : ℕ → LevelX
  | 0 => ⟨tr0M (kapD 1) 4 (colBD 1) (strD 1) (F.hi 0) (colBD 0) (strD 0) (ht6 0) (wB6 0) (bfD 0) (F.ch 0)
      (tbD 0) (tSD 0), gsD 0, BD 0, colBD 0, strD 0⟩
  | 4 => ⟨trF (kapD 4) 4 F.s (colBD 4) (strD 4) (ht6 4) (bfD 4) (F.ch 4) (tbD 4) (tSD 4), gsD 4, BD 4,
      colBD 4, strD 4⟩
  | i => ⟨trM (kapD (i + 1)) 4 4 (colBD (i + 1)) (strD (i + 1)) (F.hi i) (colBD i) (strD i) (ht6 i) (bfD i)
      (F.ch i) (tbD i) (tSD i), gsD i, BD i, colBD i, strD i⟩

/-- **The level-0 map**: stack slot `m` from level 0's column `2m` (lane `m`, real part). -/
def finX : XIR := finIR (fun m ↦ colBD 0 + strD 0 * (2 * m)) 34

/-! ## Groups and levels within budget -/

theorem dD_le {i : ℕ} (hi : i < 5) : dD i + 3 ≤ 2 ^ ht6 i := by
  interval_cases i <;> decide +kernel

theorem sbPart {i : ℕ} (hi : i < 5) (B colB str tS K n : ℕ) (hK : K ≤ n) (hK64 : K < 2 ^ 64) :
    LoopPart (sbIR (ht6 i + 1) (ht6 i) B colB str (dD i) tS K) (sbCap i n) where
  wf := wf_sbIR ..
  noLoopT := noLoopT_sbIR ..
  outs t := outs_sbIR _ _ _ _ _ _ _ _ t
  cost t := by
    have hd := dD_le hi
    have h21 := ht6_le i
    have hp : 2 ^ ht6 i ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) h21
    have e21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
    have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    rw [cost_sbIR _ _ _ _ _ _ _ _ t (by omega) (lt_of_le_of_lt hp (by norm_num)) (by omega) hK64]
    have h1 := sbCost_le (K := K) h21 (show dD i + 1 ≤ 2 ^ ht6 i by omega)
    have h2 := Nat.mul_le_mul_right (2 ^ (ht6 i + 13)) hK
    simp only [sbCap]
    omega
  low := allBelow_sbIR ..

theorem grpOk {i : ℕ} (hi : i < 5) (nr n K : ℕ) (hK : K ≤ n) (hK64 : K < 2 ^ 64) (hn : n ≤ lns i) :
    GroupOk i (grpD i nr n K) :=
  ⟨sbPart hi _ _ _ _ K n hK hK64, ⟨ldF_part _ _ (ht6_le i), allBelow_ldF ..⟩, dD_le hi, hn⟩

theorem groupOk {i : ℕ} (hi : i < 5) : ∀ g ∈ gsD i, GroupOk i g := by
  intro g hg
  rcases i with _ | i
  · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact grpOk hi _ _ _ (by norm_num) (by norm_num) (by simp [lns])
  · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact grpOk hi _ _ _ (by norm_num) (by norm_num) (by simp [lns])

theorem trPart (F : FrontA) {i : ℕ} (hi : i < 5) : PartOk (LvD F i).tr trCap := by
  interval_cases i
  · exact tr0M_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trF_part _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)

/-- **`LevelOk` at levels 1–4.** -/
theorem levelOk (F : FrontA) {i : ℕ} (h1 : 1 ≤ i) (hi : i < 5) : LevelOk i (LvD F i) := by
  refine ⟨trPart F hi, ?_, ?_, ?_, ?_⟩
  · have := groupOk hi
    interval_cases i <;> exact this
  all_goals interval_cases i <;> simp [LvD, gsD, grpD, rds, lns]

/-- Level 0's columns: `4 + 8 + 16 + 32 + 64 + 67 = 191`. -/
theorem lanesD_0 (F : FrontA) : ((LvD F 0).gs.map fun g ↦ g.nr * g.n).sum = 191 := by
  simp [LvD, gsD, grpD]

/-- **`LevelOk 0` fails**: X9's tables make round `r` compare `2·2^r` columns and decode `2·2^(r+1)`, so `GrpOK`
needs at least `4 + 8 + 16 + 32 + 64 + 64 = 188` columns at level 0, over `lns 0 = 130` (X2's six "window
lanes" at the last round); `descOk6` holds nonetheless. -/
theorem not_levelOk_0 (F : FrontA) : ¬ LevelOk 0 (LvD F 0) := fun h ↦ by
  have := h.lanes
  rw [lanesD_0] at this
  simp [lns] at this

/-! ## Sizes -/

theorem sizeIR_finIR (src : ℕ → ℕ) : ∀ k, sizeIR (finIR src k) = 1 + 31 * k
  | 0 => rfl
  | k + 1 => by
    simp only [finIR, sizeIR, sizeIR_finIR src k]
    rw [show sizeIR (mcpIR stride6 (src k) 1 (colB6 + k * stride6)) = 30 from rfl]
    ring

theorem levelSz (F : FrontA) {i : ℕ} (hi : i < 5) : LevelSz i (LvD F i) := by
  have hsb : ∀ g ∈ gsD i, sizeIR g.sb ≤ sbSz := by
    intro g hg
    have e1 : sizeIR (wtabNIR (ht6 i + 1) (tbA' (BD i) (ht6 i))) ≤ 8000 := by
      interval_cases i <;> decide +kernel
    have e2 : sizeIR (fwdNIR (ht6 i + 1) (ht6 i) (tbA' (BD i) (ht6 i))) ≤ 7000 := by
      interval_cases i <;> decide +kernel
    have key : ∀ K, sizeIR (sbIR (ht6 i + 1) (ht6 i) (BD i) (colBD i) (strD i) (dD i) (tSD i) K) ≤ sbSz :=
      fun K ↦ by
        have := sizeIR_sbIR_le (ht6 i + 1) (ht6 i) (BD i) (colBD i) (strD i) (dD i) (tSD i) K
        simp only [sbSz]; omega
    rcases i with _ | i
    · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key _
    · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact key _
  have hld : ∀ g ∈ gsD i, sizeIR g.ld ≤ ldSz := by
    intro g hg
    have key : sizeIR (ldF (tbD i) (BD i) (ht6 i)) ≤ ldSz := by rw [sizeIR_ldF]; simp only [ldSz]; norm_num
    rcases i with _ | i
    · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key
    · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact key
  interval_cases i
  · exact ⟨sizeIR_tr0M_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num), hsb, hld, by simp [LvD, gsD, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [LvD, gsD, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [LvD, gsD, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [LvD, gsD, gCap]⟩
  · exact ⟨sizeIR_trF_le _ _ _ _ _ _ _ _ _ _ (by norm_num), hsb, hld, by simp [LvD, gsD, gCap]⟩

/-- **The descent fits `2^19` statements** (`P17`). -/
theorem sizeIR_desc (F : FrontA) : sizeIR (descX6 (LvD F) finX) ≤ 2 ^ 19 :=
  sizeIR_descX6_le (fun i hi ↦ levelSz F hi) (by rw [finX, sizeIR_finIR]; simp only [finSz]; norm_num)

/-! ## `DescOk6` -/

theorem levelX_struct' {i : ℕ} {L : LevelX} (htr : PartOk L.tr trCap) (hg : ∀ g ∈ L.gs, GroupOk i g) :
    WF (levelX i L) ∧ NoLoopT (levelX i L) ∧ ∀ t, outs (levelX i L) t = 0 := by
  obtain ⟨a, b, c⟩ := groupsX_struct i L.B L.colB L.str L.gs hg
  exact ⟨⟨htr.wf, by simp +decide [WF], a⟩, ⟨htr.noLoopT, trivial, b⟩,
    fun t ↦ by simp only [levelX, outs, htr.outs, c, Nat.add_zero]⟩

/-- A level's cost from its actual rounds and columns (no `LevelOk` needed). -/
theorem cost_levelX_le' {i : ℕ} {L : LevelX} (htr : PartOk L.tr trCap) (hg : ∀ g ∈ L.gs, GroupOk i g)
    (hnr : ∀ g ∈ L.gs, g.nr ≤ rds i) (t : ℕ) :
    cost (levelX i L) t ≤ trCap + 4 +
      (L.gs.map GroupX.nr).sum * (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
        (L.gs.map fun g ↦ g.nr * g.n).sum * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 +
          13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13)) + 11 * L.gs.length := by
  have h1 := cost_groupsX_le i L.B L.colB L.str t L.gs fun g hg' ↦ ⟨hg g hg', hnr g hg'⟩
  have h4 := htr.cost t
  have e : cost (.blk [.const rRd 0]) t = 1 := rfl
  simp only [levelX, cost] at e ⊢
  omega

/-- A level's bound at its actual rounds `R`, columns `Ln` and groups `G` (`cost_levelX_le'`). -/
def lvB (i R Ln G : ℕ) : ℕ :=
  trCap + 4 + R * (lamCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + 2 ^ 27 + 23) +
    Ln * (laneCost (ht6 i + 1) (ht6 i) (2 ^ ht6 i) + ldCap + 25 + 13 * 2 ^ ht6 i + 2 ^ (ht6 i + 13)) + 11 * G

/-- The numbers: five levels at their actual rounds and columns, and `fin`, within `descCost6 + 2^43`. -/
theorem budgetD :
    lvB 0 6 191 6 + lvB 1 4 128 1 + lvB 2 4 128 1 + lvB 3 4 128 1 + lvB 4 4 128 1 + finCap + 5 ≤
      descCost6 + 2 ^ 43 := by
  simp only [lvB, descCost6, descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC,
    trCap, ldCap, finCap]
  norm_num

theorem nrD {i : ℕ} (hi : i < 5) : ∀ g ∈ gsD i, g.nr ≤ rds i := by
  intro g hg
  rcases i with _ | i
  · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [grpD, rds]
  · simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; simp [grpD, rds]

theorem cost_descX6 (L : ℕ → LevelX) (fin : XIR) (t : ℕ) : cost (descX6 L fin) t =
    cost (levelX 4 (L 4)) t + (cost (levelX 3 (L 3)) t + (cost (levelX 2 (L 2)) t + (cost (levelX 1 (L 1)) t +
      (cost (levelX 0 (L 0)) t + cost fin t + 1) + 1) + 1) + 1) + 1 := rfl

/-- **`DescOk6` of the descent** (`P17`). -/
theorem descOk6 (F : FrontA) : DescOk6 (descX6 (LvD F) finX) := by
  have hg : ∀ i < 5, ∀ g ∈ (LvD F i).gs, GroupOk i g := fun i hi ↦ by
    have := groupOk hi; interval_cases i <;> exact this
  have hn : ∀ i < 5, ∀ g ∈ (LvD F i).gs, g.nr ≤ rds i := fun i hi ↦ by
    have := nrD hi; interval_cases i <;> exact this
  obtain ⟨w4, n4, o4⟩ := levelX_struct' (trPart F (i := 4) (by norm_num)) (hg 4 (by norm_num))
  obtain ⟨w3, n3, o3⟩ := levelX_struct' (trPart F (i := 3) (by norm_num)) (hg 3 (by norm_num))
  obtain ⟨w2, n2, o2⟩ := levelX_struct' (trPart F (i := 2) (by norm_num)) (hg 2 (by norm_num))
  obtain ⟨w1, n1, o1⟩ := levelX_struct' (trPart F (i := 1) (by norm_num)) (hg 1 (by norm_num))
  obtain ⟨w0, n0, o0⟩ := levelX_struct' (trPart F (i := 0) (by norm_num)) (hg 0 (by norm_num))
  have hf := finIR_part34 (fun m ↦ colBD 0 + strD 0 * (2 * m))
  refine ⟨⟨w4, w3, w2, w1, w0, hf.wf⟩, ⟨n4, n3, n2, n1, n0, hf.noLoopT⟩, fun t ↦ ?_, fun t ↦ ?_⟩
  · have of : outs finX t = 0 := hf.outs t
    simp only [descX6, outs, o4, o3, o2, o1, o0, of]
  · have c0 : cost (levelX 0 (LvD F 0)) t ≤ lvB 0 6 191 6 := by
      have h := cost_levelX_le' (trPart F (i := 0) (by norm_num)) (hg 0 (by norm_num)) (hn 0 (by norm_num)) t
      have e1 : ((LvD F 0).gs.map GroupX.nr).sum = 6 := by simp [LvD, gsD, grpD]
      have e2 : ((LvD F 0).gs.map fun g ↦ g.nr * g.n).sum = 191 := by simp [LvD, gsD, grpD]
      have e3 : (LvD F 0).gs.length = 6 := by simp [LvD, gsD]
      rw [e1, e2, e3] at h
      exact h
    have c1 : cost (levelX 1 (LvD F 1)) t ≤ lvB 1 4 128 1 := by
      have h := cost_levelX_le' (trPart F (i := 1) (by norm_num)) (hg 1 (by norm_num)) (hn 1 (by norm_num)) t
      have e1 : ((LvD F 1).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
      have e2 : ((LvD F 1).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
      have e3 : (LvD F 1).gs.length = 1 := by simp [LvD, gsD]
      rw [e1, e2, e3] at h
      exact h
    have c2 : cost (levelX 2 (LvD F 2)) t ≤ lvB 2 4 128 1 := by
      have h := cost_levelX_le' (trPart F (i := 2) (by norm_num)) (hg 2 (by norm_num)) (hn 2 (by norm_num)) t
      have e1 : ((LvD F 2).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
      have e2 : ((LvD F 2).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
      have e3 : (LvD F 2).gs.length = 1 := by simp [LvD, gsD]
      rw [e1, e2, e3] at h
      exact h
    have c3 : cost (levelX 3 (LvD F 3)) t ≤ lvB 3 4 128 1 := by
      have h := cost_levelX_le' (trPart F (i := 3) (by norm_num)) (hg 3 (by norm_num)) (hn 3 (by norm_num)) t
      have e1 : ((LvD F 3).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
      have e2 : ((LvD F 3).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
      have e3 : (LvD F 3).gs.length = 1 := by simp [LvD, gsD]
      rw [e1, e2, e3] at h
      exact h
    have c4 : cost (levelX 4 (LvD F 4)) t ≤ lvB 4 4 128 1 := by
      have h := cost_levelX_le' (trPart F (i := 4) (by norm_num)) (hg 4 (by norm_num)) (hn 4 (by norm_num)) t
      have e1 : ((LvD F 4).gs.map GroupX.nr).sum = 4 := by simp [LvD, gsD, grpD]
      have e2 : ((LvD F 4).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [LvD, gsD, grpD]
      have e3 : (LvD F 4).gs.length = 1 := by simp [LvD, gsD]
      rw [e1, e2, e3] at h
      exact h
    have cf : cost finX t ≤ finCap := hf.cost t
    have hb := budgetD
    rw [cost_descX6]
    omega

/-! ## Layout facts -/

/-- **The layout facts** `levelX_cols` and `groupSem_L` need, at every level. -/
theorem layoutD {i : ℕ} (hi : i < 5) :
    ht6 i + 1 ≤ 64 ∧ regs ≤ BD i ∧ fdEnd (BD i) (ht6 i) < 2 ^ 64 ∧
      (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i ∧ dD i + 3 ≤ 2 ^ ht6 i ∧ fdEnd (BD i) (ht6 i) ≤ colBD i ∧
      2 ^ ht6 i ≤ strD i ∧ regs ≤ tbD i ∧ regs ≤ tSD i ∧ tbD i + 2 * rndD i ≤ tSD i ∧
      tSD i + 2 * rndD i + 1 < BD i ∧ colBD i + strD i * 67 ≤ 2 ^ 30 := by
  interval_cases i <;> decide +kernel

/-- **The glue's layout facts** at levels 0–3 (from level `i + 1`'s columns): `κ_i = 4 + κ_{i+1}`, the start
columns' two rows hold `2^κ + ℓ` coefficients, the regions are disjoint and inside `2^30`. -/
theorem glueLay {i : ℕ} (hi : i < 4) :
    kapD i = 4 + kapD (i + 1) ∧ regs ≤ colBD i ∧ regs ≤ colBD (i + 1) ∧
      2 ^ (4 + kapD (i + 1)) + rndD i ≤ strD i ∧ 2 ^ kapD (i + 1) ≤ strD (i + 1) ∧
      colBD i + 3 * strD i < 2 ^ 64 ∧ colBD (i + 1) + strD (i + 1) * (2 * 2 ^ 4) < 2 ^ 64 ∧
      colBD i + 2 * strD i ≤ 2 ^ 30 ∧
      (colBD i + 2 * strD i ≤ colBD (i + 1) ∨ colBD (i + 1) + strD (i + 1) * (2 * 2 ^ 4) ≤ colBD i) := by
  interval_cases i <;> decide +kernel

/-! ## `GrpsOK` from X9's tables -/

/-- **A group's `GrpOK`** from the round tables (`TabW`) and per-round numeric layout facts. -/
theorem grpOK_of {M₀ : Mem} {N ℓ B colB str d tb tS J : ℕ} {bf : ℕ → ℕ} {C₀ : ℕ → ℕ → BF64} {nc : ℕ → ℕ}
    {sz : ℕ} {g : GroupX} {r K : ℕ} (hT : TabW M₀ J 0 tb tS bf J) (hbf : ∀ k ≤ J, bf k < 2 ^ 64) (hJ : J < 63)
    (hsb : g.sb = sbIR N ℓ B colB str d tS K) (hld : g.ld = ldF tb B ℓ) (hm : g.m = d + 3) (hK : K < 2 ^ 64)
    (h64 : colB + str * g.n < 2 ^ 64) (hsz : colB + str * g.n ≤ sz) (hr : r + g.nr ≤ J)
    (hR : ∀ j < g.nr, tS + 2 * (r + j) + 1 < B ∧ tb + 2 * (r + j) + 2 ≤ B ∧ 2 * 2 ^ (r + j) ≤ K ∧
      2 * 2 ^ (r + j) ≤ nc (r + j) ∧ nc (r + j) ≤ g.n ∧ nc (r + (j + 1)) ≤ g.n ∧ 2 * 2 ^ (1 + (r + j)) ≤ 4096 ∧
      regs ≤ bf (J - (r + j)) ∧ bf (J - (r + j)) + 2 * 2 ^ (r + j) * 2 ^ ℓ ≤ B ∧
      regs ≤ bf (J - 1 - (r + j)) ∧ bf (J - 1 - (r + j)) + g.n + 2 * 2 ^ (1 + (r + j)) * (2 ^ ℓ - 1) ≤ B)
    (hL : ∀ j < g.nr, (sbList M₀ N ℓ d tS (r + j) (colsL M₀ N ℓ d tb tS C₀ (r + j))).length = d + 3) :
    GrpOK M₀ N ℓ B colB str d tb tS C₀ nc sz g r := by
  refine ⟨K, hsb, hld, hm, hK, h64, hsz, by omega, fun j hj ↦ ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := TabW.entries hT hbf (by omega) (r := r + j) (by omega) (by omega)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hR j hj
  rw [a1, a2, a3, a4]
  simp only [Nat.zero_add]
  refine ⟨b1, b2, b3, b4, b5, b6, b7, fun q hq p hp ↦ ?_, fun q hq ↦ ⟨by omega, fun p hp ↦ ?_⟩, hL j hj⟩
  · have := Nat.mul_le_mul_left (2 * 2 ^ (r + j)) (show p + 1 ≤ 2 ^ ℓ by omega)
    rw [Nat.mul_succ] at this
    omega
  · have := Nat.mul_le_mul_left (2 * 2 ^ (1 + (r + j))) (show p ≤ 2 ^ ℓ - 1 by omega)
    omega

/-- **`GrpsOK` at every level** from X9's round tables (`TabW`, as `trIR_sem` leaves them), a heap of at least
`2^30` words, and the agreement fact (each round's list has `d + 3` positions). -/
theorem grpsOK {i : ℕ} (hi : i < 5) {M₀ : Mem} (C₀ : ℕ → ℕ → BF64) {sz : ℕ} (hsz : 2 ^ 30 ≤ sz)
    (hT : TabW M₀ (rndD i) 0 (tbD i) (tSD i) (bfD i) (rndD i))
    (hL : ∀ r < rndD i, (sbList M₀ (ht6 i + 1) (ht6 i) (dD i) (tSD i) r
      (colsL M₀ (ht6 i + 1) (ht6 i) (dD i) (tbD i) (tSD i) C₀ r)).length = dD i + 3) :
    GrpsOK M₀ (ht6 i + 1) (ht6 i) (BD i) (colBD i) (strD i) (dD i) (tbD i) (tSD i) C₀ (ncD i) sz
      (gsD i) 0 := by
  have hbf : ∀ k ≤ rndD i, bfD i k < 2 ^ 64 := fun k hk ↦ by
    interval_cases i <;> simp only [rndD] at hk <;> interval_cases k <;> decide +kernel
  have hR : rndD i < 63 := by interval_cases i <;> decide +kernel
  have hL' : ∀ r j, r + j < rndD i → (sbList M₀ (ht6 i + 1) (ht6 i) (dD i) (tSD i) (r + j)
      (colsL M₀ (ht6 i + 1) (ht6 i) (dD i) (tbD i) (tSD i) C₀ (r + j))).length = dD i + 3 :=
    fun r j h ↦ hL (r + j) h
  interval_cases i
  · simp only [gsD, GrpsOK]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      refine grpOK_of hT hbf hR rfl rfl rfl (by decide) (by decide) (le_trans (by decide) hsz) (by decide)
        (fun j hj ↦ ?_) (fun j hj ↦ hL' _ _ (by simp only [grpD, rndD] at hj ⊢; omega)) <;>
      simp only [grpD] at hj <;> interval_cases j <;> decide +kernel
  all_goals
    simp only [gsD, GrpsOK]
    refine ⟨grpOK_of hT hbf hR rfl rfl rfl (by decide) (by decide) (le_trans (by decide) hsz) (by decide)
      (fun j hj ↦ ?_) (fun j hj ↦ hL' _ _ (by simp only [grpD, rndD] at hj ⊢; omega)), trivial⟩
    simp only [grpD] at hj
    interval_cases j <;> decide +kernel

/-! ## The starts are W1's -/

section W1

open LeanVM.Parameters LeanVM.Protocol.Whir

/-- **Level 0 starts from W1's candidate**: `candC (kapD 0)` holds `mid0`'s `cand hi U` for level 1's decoded `U`. -/
theorem rep_start_0 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 14 - 1 + 4) Tc U)
    (hi : List E2) : RepT (dD 0) (candC (kapD 0) Tc hi) (Lvm6.Whir.mid0.L.cand hi U) :=
  rep_cand (ko := 17) (ℓ := 6) (h := 20) (κ' := 14) (ℓ' := 4) (h' := 19) (kq := 18) (t := 110) (c := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 1 starts from `mid1`'s candidate. -/
theorem rep_start_1 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 10 - 1 + 4) Tc U)
    (hi : List E2) : RepT (dD 1) (candC (kapD 1) Tc hi) (Lvm6.Whir.mid1.L.cand hi U) :=
  rep_cand (ko := 13) (ℓ := 4) (h := 19) (κ' := 10) (ℓ' := 4) (h' := 18) (kq := 7) (t := 45) (c := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 2 starts from `mid2`'s candidate. -/
theorem rep_start_2 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 6 - 1 + 4) Tc U)
    (hi : List E2) : RepT (dD 2) (candC (kapD 2) Tc hi) (Lvm6.Whir.mid2.L.cand hi U) :=
  rep_cand (ko := 9) (ℓ := 4) (h := 18) (κ' := 6) (ℓ' := 4) (h' := 17) (kq := 3) (t := 28) (c := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 3 starts from `mid3`'s candidate. -/
theorem rep_start_3 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 2 - 1 + 4) Tc U)
    (hi : List E2) : RepT (dD 3) (candC (kapD 3) Tc hi) (Lvm6.Whir.mid3.L.cand hi U) :=
  rep_cand (ko := 5) (ℓ := 4) (h := 17) (κ' := 2) (ℓ' := 4) (h' := 16) (kq := 2) (t := 21) (c := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- **Level 4 starts from W1's final polynomial**: its coefficients are `s`. -/
theorem rep_start_4 (s : List E2) : RepT (dD 4) (fun _ x ↦ s.getD x 0) (Lvm6.Whir.finD.Fv.fpoly s) :=
  rep_fpoly (κ := 2) (ℓ := 4) (by norm_num) (by norm_num) s

end W1

end Lvm6.X
