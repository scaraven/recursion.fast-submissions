-- lvm6 EXG (DP6 §2 item 3): the concrete descent at `P18`. Per level a layout (buffers, tables, scratch, columns)
-- in the `2^30` words, the groups (level 0: six one-round groups of 4, 8, 16, 32, 64, 67 columns; levels 1–4: one
-- group of four rounds × 32 columns), the transitions with the level glue (`tr0M`, `trM`, `trF`) and `finX18`
-- (`finIR`, the 34 stack slots from level 0's real columns). Proved: `GroupOk` of every group, `LevelOk` at levels
-- 1–4, `LevelSz`, `sizeIR ≤ 2^19`, **`DescOk6`** (directly: level 0's 191 columns exceed `lns 0 = 130`, so `LevelOk 0`
-- fails — `not_levelOk18_0` — but the whole descent is within `descCost6 + 2^43`), the layout facts `levelX_cols`
-- and `glueIR_cols` need, and `GrpsOK` from X9's tables and the agreement fact (`grpsOK18`). New.
import Lvm6XGlue

/-!
# The descent at `P18`

* `kap18 i`, `rnd18 i`, `d18 i = 2^κ − 1 + ℓ`: W1's `lad18` levels `(κ, ℓ) = (19,6), (15,4), (11,4), (7,4), (3,4)`.
* Layout: `bf18 i k` (buffer `k`, `bsz` words; levels 1–4 buffer `0` is the committed rows `wB6 i`), `tb18`, `tS18`,
  `B18`, `colB18`, `str18 i = 2^ht6 i`. Level 0 (last in time) uses `[2^28, 2^30)` and `[wB6 0 + 46·2^21, 2^28)`;
  levels 1–4 sit above the rows in `[331350016, 470696192 + 32·2^17)`.
* `gs18`, `nc18` (columns at round `r`: `2·2^r`; level 0 ends with 67 = lanes `0 … 33` real and imaginary, enough
  for the 34 stack slots), `FrontA` (the cells the front fills: challenge pairs, high parts, final scalars), `Lv18`,
  `finX18`.
* **`groupOk18`**, **`levelOk18`** (`1 ≤ i < 5`), **`not_levelOk18_0`**, **`levelSz18`**, **`sizeIR_desc18`**,
  **`descOk6_18`**, **`grpsOK18`**, `layout18`, `glueLay18`; `rep_start18_0 … _4`: the starts are W1's
  `mid0 … mid3` candidates and `fin18`'s final polynomial (`rep_cand`, `rep_fpoly`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-! ## Parameters -/

/-- Level `i`'s message variables (W1's `lad18`). -/
def kap18 : ℕ → ℕ
  | 0 => 19
  | 1 => 15
  | 2 => 11
  | 3 => 7
  | _ => 3

/-- Level `i`'s fold rounds. -/
def rnd18 : ℕ → ℕ
  | 0 => 6
  | _ => 4

/-- Level `i`'s degree `2^κ − 1 + ℓ`. -/
def d18 (i : ℕ) : ℕ := 2 ^ kap18 i - 1 + rnd18 i

/-! ## The layout -/

/-- Buffer `k` of level `i` (`bsz (ht6 i) 0 (rnd18 i) k` words). -/
def bf18 : ℕ → ℕ → ℕ
  | 0, k => [268435456, 536870912, 671088640, 738197504, 234881024, 251658240, 260046848].getD k 0
  | 1, k => [268435456, 331350016, 348127232, 356515840, 360710144].getD k 0
  | 2, k => [301989888, 407900224, 416288832, 420483136, 422580288].getD k 0
  | 3, k => [318767104, 446177408, 450371712, 452468864, 453517440].getD k 0
  | _, k => [327155712, 465318080, 467415232, 468463808, 468988096].getD k 0

/-- The loaders' table. -/
def tb18 : ℕ → ℕ
  | 0 => 264241152
  | 1 => 362807296
  | 2 => 423628864
  | 3 => 454041728
  | _ => 469250240

/-- The builder's table. -/
def tS18 (i : ℕ) : ℕ := tb18 i + 16

/-- The decoder's scratch. -/
def B18 : ℕ → ℕ
  | 0 => 771751936
  | 1 => 362807360
  | 2 => 423628928
  | 3 => 454041792
  | _ => 469250304

/-- The columns. -/
def colB18 : ℕ → ℕ
  | 0 => 805306368
  | 1 => 374345792
  | 2 => 429400192
  | 3 => 456929472
  | _ => 470696192

/-- The column stride. -/
def str18 (i : ℕ) : ℕ := 2 ^ ht6 i

/-! ## The groups -/

/-- A group of level `i`: `nr` rounds of `n` columns, the builder's lane bound `K`. -/
def grp18 (i nr n K : ℕ) : GroupX :=
  ⟨sbIR (ht6 i + 1) (ht6 i) (B18 i) (colB18 i) (str18 i) (d18 i) (tS18 i) K, ldF (tb18 i) (B18 i) (ht6 i), nr, n,
    d18 i + 3⟩

/-- Level `i`'s groups. -/
def gs18 : ℕ → List GroupX
  | 0 => [grp18 0 1 4 2, grp18 0 1 8 4, grp18 0 1 16 8, grp18 0 1 32 16, grp18 0 1 64 32, grp18 0 1 67 64]
  | i + 1 => [grp18 (i + 1) 4 32 16]

/-- The columns at round `r` of level `i`. -/
def nc18 (i r : ℕ) : ℕ := if i = 0 ∧ r = 6 then 67 else 2 * 2 ^ r

/-- **The cells the front fills**: the challenge pairs `ch i k` (W1's `(α, β)` of round `k` of level `i`, two `E2`),
the high parts `hi i` (`E2` scalar `k` at `hi i + 2k`), the final scalars `s`. -/
structure FrontA where
  ch : ℕ → ℕ → ℕ
  hi : ℕ → ℕ
  s : ℕ

/-- **The levels at `P18`**: level 0 glues level 1's columns and expands the committed rows; levels 1–3 glue the
next level's columns; level 4 starts from `s`. -/
def Lv18 (F : FrontA) : ℕ → LevelX
  | 0 => ⟨tr0M (kap18 1) 4 (colB18 1) (str18 1) (F.hi 0) (colB18 0) (str18 0) (ht6 0) (wB6 0) (bf18 0) (F.ch 0)
      (tb18 0) (tS18 0), gs18 0, B18 0, colB18 0, str18 0⟩
  | 4 => ⟨trF (kap18 4) 4 F.s (colB18 4) (str18 4) (ht6 4) (bf18 4) (F.ch 4) (tb18 4) (tS18 4), gs18 4, B18 4,
      colB18 4, str18 4⟩
  | i => ⟨trM (kap18 (i + 1)) 4 4 (colB18 (i + 1)) (str18 (i + 1)) (F.hi i) (colB18 i) (str18 i) (ht6 i) (bf18 i)
      (F.ch i) (tb18 i) (tS18 i), gs18 i, B18 i, colB18 i, str18 i⟩

/-- **The level-0 map**: stack slot `m` from level 0's column `2m` (lane `m`, real part). -/
def finX18 : XIR := finIR (fun m ↦ colB18 0 + str18 0 * (2 * m)) 34

/-! ## Groups and levels within budget -/

theorem d18_le {i : ℕ} (hi : i < 5) : d18 i + 3 ≤ 2 ^ ht6 i := by
  interval_cases i <;> decide +kernel

theorem sbPart18 {i : ℕ} (hi : i < 5) (B colB str tS K n : ℕ) (hK : K ≤ n) (hK64 : K < 2 ^ 64) :
    LoopPart (sbIR (ht6 i + 1) (ht6 i) B colB str (d18 i) tS K) (sbCap i n) where
  wf := wf_sbIR ..
  noLoopT := noLoopT_sbIR ..
  outs t := outs_sbIR _ _ _ _ _ _ _ _ t
  cost t := by
    have hd := d18_le hi
    have h21 := ht6_le i
    have hp : 2 ^ ht6 i ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) h21
    have e21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
    have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    rw [cost_sbIR _ _ _ _ _ _ _ _ t (by omega) (lt_of_le_of_lt hp (by norm_num)) (by omega) hK64]
    have h1 := sbCost_le (K := K) h21 (show d18 i + 1 ≤ 2 ^ ht6 i by omega)
    have h2 := Nat.mul_le_mul_right (2 ^ (ht6 i + 13)) hK
    simp only [sbCap]
    omega
  low := allBelow_sbIR ..

theorem grpOk18 {i : ℕ} (hi : i < 5) (nr n K : ℕ) (hK : K ≤ n) (hK64 : K < 2 ^ 64) (hn : n ≤ lns i) :
    GroupOk i (grp18 i nr n K) :=
  ⟨sbPart18 hi _ _ _ _ K n hK hK64, ⟨ldF_part _ _ (ht6_le i), allBelow_ldF ..⟩, d18_le hi, hn⟩

theorem groupOk18 {i : ℕ} (hi : i < 5) : ∀ g ∈ gs18 i, GroupOk i g := by
  intro g hg
  rcases i with _ | i
  · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact grpOk18 hi _ _ _ (by norm_num) (by norm_num) (by simp [lns])
  · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact grpOk18 hi _ _ _ (by norm_num) (by norm_num) (by simp [lns])

theorem trPart18 (F : FrontA) {i : ℕ} (hi : i < 5) : PartOk (Lv18 F i).tr trCap := by
  interval_cases i
  · exact tr0M_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trM_part _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by norm_num) (by decide)
  · exact trF_part _ _ _ _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)

/-- **`LevelOk` at levels 1–4.** -/
theorem levelOk18 (F : FrontA) {i : ℕ} (h1 : 1 ≤ i) (hi : i < 5) : LevelOk i (Lv18 F i) := by
  refine ⟨trPart18 F hi, ?_, ?_, ?_, ?_⟩
  · have := groupOk18 hi
    interval_cases i <;> exact this
  all_goals interval_cases i <;> simp [Lv18, gs18, grp18, rds, lns]

/-- Level 0's columns: `4 + 8 + 16 + 32 + 64 + 67 = 191`. -/
theorem lanes18_0 (F : FrontA) : ((Lv18 F 0).gs.map fun g ↦ g.nr * g.n).sum = 191 := by
  simp [Lv18, gs18, grp18]

/-- **`LevelOk 0` fails**: X9's tables make round `r` compare `2·2^r` columns and decode `2·2^(r+1)`, so `GrpOK`
needs at least `4 + 8 + 16 + 32 + 64 + 64 = 188` columns at level 0, over `lns 0 = 130` (X2's six "window
lanes" at the last round); `descOk6_18` holds nonetheless. -/
theorem not_levelOk18_0 (F : FrontA) : ¬ LevelOk 0 (Lv18 F 0) := fun h ↦ by
  have := h.lanes
  rw [lanes18_0] at this
  simp [lns] at this

/-! ## Sizes -/

theorem sizeIR_finIR (src : ℕ → ℕ) : ∀ k, sizeIR (finIR src k) = 1 + 31 * k
  | 0 => rfl
  | k + 1 => by
    simp only [finIR, sizeIR, sizeIR_finIR src k]
    rw [show sizeIR (mcpIR stride6 (src k) 1 (colB6 + k * stride6)) = 30 from rfl]
    ring

theorem levelSz18 (F : FrontA) {i : ℕ} (hi : i < 5) : LevelSz i (Lv18 F i) := by
  have hsb : ∀ g ∈ gs18 i, sizeIR g.sb ≤ sbSz := by
    intro g hg
    have e1 : sizeIR (wtabNIR (ht6 i + 1) (tbA' (B18 i) (ht6 i))) ≤ 8000 := by
      interval_cases i <;> decide +kernel
    have e2 : sizeIR (fwdNIR (ht6 i + 1) (ht6 i) (tbA' (B18 i) (ht6 i))) ≤ 7000 := by
      interval_cases i <;> decide +kernel
    have key : ∀ K, sizeIR (sbIR (ht6 i + 1) (ht6 i) (B18 i) (colB18 i) (str18 i) (d18 i) (tS18 i) K) ≤ sbSz :=
      fun K ↦ by
        have := sizeIR_sbIR_le (ht6 i + 1) (ht6 i) (B18 i) (colB18 i) (str18 i) (d18 i) (tS18 i) K
        simp only [sbSz]; omega
    rcases i with _ | i
    · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key _
    · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact key _
  have hld : ∀ g ∈ gs18 i, sizeIR g.ld ≤ ldSz := by
    intro g hg
    have key : sizeIR (ldF (tb18 i) (B18 i) (ht6 i)) ≤ ldSz := by rw [sizeIR_ldF]; simp only [ldSz]; norm_num
    rcases i with _ | i
    · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key
    · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact key
  interval_cases i
  · exact ⟨sizeIR_tr0M_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num), hsb, hld, by simp [Lv18, gs18, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [Lv18, gs18, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [Lv18, gs18, gCap]⟩
  · exact ⟨sizeIR_trM_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), hsb, hld, by simp [Lv18, gs18, gCap]⟩
  · exact ⟨sizeIR_trF_le _ _ _ _ _ _ _ _ _ _ (by norm_num), hsb, hld, by simp [Lv18, gs18, gCap]⟩

/-- **The descent at `P18` fits `2^19` statements.** -/
theorem sizeIR_desc18 (F : FrontA) : sizeIR (descX6 (Lv18 F) finX18) ≤ 2 ^ 19 :=
  sizeIR_descX6_le (fun i hi ↦ levelSz18 F hi) (by rw [finX18, sizeIR_finIR]; simp only [finSz]; norm_num)

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
theorem budget18 :
    lvB 0 6 191 6 + lvB 1 4 128 1 + lvB 2 4 128 1 + lvB 3 4 128 1 + lvB 4 4 128 1 + finCap + 5 ≤
      descCost6 + 2 ^ 43 := by
  simp only [lvB, descCost6, descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC,
    trCap, ldCap, finCap]
  norm_num

theorem nr18 {i : ℕ} (hi : i < 5) : ∀ g ∈ gs18 i, g.nr ≤ rds i := by
  intro g hg
  rcases i with _ | i
  · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [grp18, rds]
  · simp only [gs18, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; simp [grp18, rds]

theorem cost_descX6 (L : ℕ → LevelX) (fin : XIR) (t : ℕ) : cost (descX6 L fin) t =
    cost (levelX 4 (L 4)) t + (cost (levelX 3 (L 3)) t + (cost (levelX 2 (L 2)) t + (cost (levelX 1 (L 1)) t +
      (cost (levelX 0 (L 0)) t + cost fin t + 1) + 1) + 1) + 1) + 1 := rfl

/-- **`DescOk6` of the descent at `P18`.** -/
theorem descOk6_18 (F : FrontA) : DescOk6 (descX6 (Lv18 F) finX18) := by
  have hg : ∀ i < 5, ∀ g ∈ (Lv18 F i).gs, GroupOk i g := fun i hi ↦ by
    have := groupOk18 hi; interval_cases i <;> exact this
  have hn : ∀ i < 5, ∀ g ∈ (Lv18 F i).gs, g.nr ≤ rds i := fun i hi ↦ by
    have := nr18 hi; interval_cases i <;> exact this
  obtain ⟨w4, n4, o4⟩ := levelX_struct' (trPart18 F (i := 4) (by norm_num)) (hg 4 (by norm_num))
  obtain ⟨w3, n3, o3⟩ := levelX_struct' (trPart18 F (i := 3) (by norm_num)) (hg 3 (by norm_num))
  obtain ⟨w2, n2, o2⟩ := levelX_struct' (trPart18 F (i := 2) (by norm_num)) (hg 2 (by norm_num))
  obtain ⟨w1, n1, o1⟩ := levelX_struct' (trPart18 F (i := 1) (by norm_num)) (hg 1 (by norm_num))
  obtain ⟨w0, n0, o0⟩ := levelX_struct' (trPart18 F (i := 0) (by norm_num)) (hg 0 (by norm_num))
  have hf := finIR_part34 (fun m ↦ colB18 0 + str18 0 * (2 * m))
  refine ⟨⟨w4, w3, w2, w1, w0, hf.wf⟩, ⟨n4, n3, n2, n1, n0, hf.noLoopT⟩, fun t ↦ ?_, fun t ↦ ?_⟩
  · have of : outs finX18 t = 0 := hf.outs t
    simp only [descX6, outs, o4, o3, o2, o1, o0, of]
  · have c0 : cost (levelX 0 (Lv18 F 0)) t ≤ lvB 0 6 191 6 := by
      have h := cost_levelX_le' (trPart18 F (i := 0) (by norm_num)) (hg 0 (by norm_num)) (hn 0 (by norm_num)) t
      have e1 : ((Lv18 F 0).gs.map GroupX.nr).sum = 6 := by simp [Lv18, gs18, grp18]
      have e2 : ((Lv18 F 0).gs.map fun g ↦ g.nr * g.n).sum = 191 := by simp [Lv18, gs18, grp18]
      have e3 : (Lv18 F 0).gs.length = 6 := by simp [Lv18, gs18]
      rw [e1, e2, e3] at h
      exact h
    have c1 : cost (levelX 1 (Lv18 F 1)) t ≤ lvB 1 4 128 1 := by
      have h := cost_levelX_le' (trPart18 F (i := 1) (by norm_num)) (hg 1 (by norm_num)) (hn 1 (by norm_num)) t
      have e1 : ((Lv18 F 1).gs.map GroupX.nr).sum = 4 := by simp [Lv18, gs18, grp18]
      have e2 : ((Lv18 F 1).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [Lv18, gs18, grp18]
      have e3 : (Lv18 F 1).gs.length = 1 := by simp [Lv18, gs18]
      rw [e1, e2, e3] at h
      exact h
    have c2 : cost (levelX 2 (Lv18 F 2)) t ≤ lvB 2 4 128 1 := by
      have h := cost_levelX_le' (trPart18 F (i := 2) (by norm_num)) (hg 2 (by norm_num)) (hn 2 (by norm_num)) t
      have e1 : ((Lv18 F 2).gs.map GroupX.nr).sum = 4 := by simp [Lv18, gs18, grp18]
      have e2 : ((Lv18 F 2).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [Lv18, gs18, grp18]
      have e3 : (Lv18 F 2).gs.length = 1 := by simp [Lv18, gs18]
      rw [e1, e2, e3] at h
      exact h
    have c3 : cost (levelX 3 (Lv18 F 3)) t ≤ lvB 3 4 128 1 := by
      have h := cost_levelX_le' (trPart18 F (i := 3) (by norm_num)) (hg 3 (by norm_num)) (hn 3 (by norm_num)) t
      have e1 : ((Lv18 F 3).gs.map GroupX.nr).sum = 4 := by simp [Lv18, gs18, grp18]
      have e2 : ((Lv18 F 3).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [Lv18, gs18, grp18]
      have e3 : (Lv18 F 3).gs.length = 1 := by simp [Lv18, gs18]
      rw [e1, e2, e3] at h
      exact h
    have c4 : cost (levelX 4 (Lv18 F 4)) t ≤ lvB 4 4 128 1 := by
      have h := cost_levelX_le' (trPart18 F (i := 4) (by norm_num)) (hg 4 (by norm_num)) (hn 4 (by norm_num)) t
      have e1 : ((Lv18 F 4).gs.map GroupX.nr).sum = 4 := by simp [Lv18, gs18, grp18]
      have e2 : ((Lv18 F 4).gs.map fun g ↦ g.nr * g.n).sum = 128 := by simp [Lv18, gs18, grp18]
      have e3 : (Lv18 F 4).gs.length = 1 := by simp [Lv18, gs18]
      rw [e1, e2, e3] at h
      exact h
    have cf : cost finX18 t ≤ finCap := hf.cost t
    have hb := budget18
    rw [cost_descX6]
    omega

/-! ## Layout facts -/

/-- **The layout facts** `levelX_cols` and `groupSem_L` need, at every level. -/
theorem layout18 {i : ℕ} (hi : i < 5) :
    ht6 i + 1 ≤ 64 ∧ regs ≤ B18 i ∧ fdEnd (B18 i) (ht6 i) < 2 ^ 64 ∧
      (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i ∧ d18 i + 3 ≤ 2 ^ ht6 i ∧ fdEnd (B18 i) (ht6 i) ≤ colB18 i ∧
      2 ^ ht6 i ≤ str18 i ∧ regs ≤ tb18 i ∧ regs ≤ tS18 i ∧ tb18 i + 2 * rnd18 i ≤ tS18 i ∧
      tS18 i + 2 * rnd18 i + 1 < B18 i ∧ colB18 i + str18 i * 67 ≤ 2 ^ 30 := by
  interval_cases i <;> decide +kernel

/-- **The glue's layout facts** at levels 0–3 (from level `i + 1`'s columns): `κ_i = 4 + κ_{i+1}`, the start
columns' two rows hold `2^κ + ℓ` coefficients, the regions are disjoint and inside `2^30`. -/
theorem glueLay18 {i : ℕ} (hi : i < 4) :
    kap18 i = 4 + kap18 (i + 1) ∧ regs ≤ colB18 i ∧ regs ≤ colB18 (i + 1) ∧
      2 ^ (4 + kap18 (i + 1)) + rnd18 i ≤ str18 i ∧ 2 ^ kap18 (i + 1) ≤ str18 (i + 1) ∧
      colB18 i + 3 * str18 i < 2 ^ 64 ∧ colB18 (i + 1) + str18 (i + 1) * (2 * 2 ^ 4) < 2 ^ 64 ∧
      colB18 i + 2 * str18 i ≤ 2 ^ 30 ∧
      (colB18 i + 2 * str18 i ≤ colB18 (i + 1) ∨ colB18 (i + 1) + str18 (i + 1) * (2 * 2 ^ 4) ≤ colB18 i) := by
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
theorem grpsOK18 {i : ℕ} (hi : i < 5) {M₀ : Mem} (C₀ : ℕ → ℕ → BF64) {sz : ℕ} (hsz : 2 ^ 30 ≤ sz)
    (hT : TabW M₀ (rnd18 i) 0 (tb18 i) (tS18 i) (bf18 i) (rnd18 i))
    (hL : ∀ r < rnd18 i, (sbList M₀ (ht6 i + 1) (ht6 i) (d18 i) (tS18 i) r
      (colsL M₀ (ht6 i + 1) (ht6 i) (d18 i) (tb18 i) (tS18 i) C₀ r)).length = d18 i + 3) :
    GrpsOK M₀ (ht6 i + 1) (ht6 i) (B18 i) (colB18 i) (str18 i) (d18 i) (tb18 i) (tS18 i) C₀ (nc18 i) sz
      (gs18 i) 0 := by
  have hbf : ∀ k ≤ rnd18 i, bf18 i k < 2 ^ 64 := fun k hk ↦ by
    interval_cases i <;> simp only [rnd18] at hk <;> interval_cases k <;> decide +kernel
  have hR : rnd18 i < 63 := by interval_cases i <;> decide +kernel
  have hL' : ∀ r j, r + j < rnd18 i → (sbList M₀ (ht6 i + 1) (ht6 i) (d18 i) (tS18 i) (r + j)
      (colsL M₀ (ht6 i + 1) (ht6 i) (d18 i) (tb18 i) (tS18 i) C₀ (r + j))).length = d18 i + 3 :=
    fun r j h ↦ hL (r + j) h
  interval_cases i
  · simp only [gs18, GrpsOK]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      refine grpOK_of hT hbf hR rfl rfl rfl (by decide) (by decide) (le_trans (by decide) hsz) (by decide)
        (fun j hj ↦ ?_) (fun j hj ↦ hL' _ _ (by simp only [grp18, rnd18] at hj ⊢; omega)) <;>
      simp only [grp18] at hj <;> interval_cases j <;> decide +kernel
  all_goals
    simp only [gs18, GrpsOK]
    refine ⟨grpOK_of hT hbf hR rfl rfl rfl (by decide) (by decide) (le_trans (by decide) hsz) (by decide)
      (fun j hj ↦ ?_) (fun j hj ↦ hL' _ _ (by simp only [grp18, rnd18] at hj ⊢; omega)), trivial⟩
    simp only [grp18] at hj
    interval_cases j <;> decide +kernel

/-! ## The starts are W1's -/

section W1

open LeanVM.Parameters LeanVM.Protocol.Whir

/-- **Level 0 starts from W1's candidate**: `candC (kap18 0)` holds `mid0`'s `cand hi U` for level 1's decoded `U`. -/
theorem rep_start18_0 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 15 - 1 + 4) Tc U)
    (hi : List E2) : RepT (d18 0) (candC (kap18 0) Tc hi) (Lvm6.Whir.mid0.L.cand hi U) :=
  rep_cand (ko := 18) (ℓ := 6) (h := 21) (κ' := 15) (ℓ' := 4) (h' := 20) (kq := 18) (t := 110) (c := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 1 starts from `mid1`'s candidate. -/
theorem rep_start18_1 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 11 - 1 + 4) Tc U)
    (hi : List E2) : RepT (d18 1) (candC (kap18 1) Tc hi) (Lvm6.Whir.mid1.L.cand hi U) :=
  rep_cand (ko := 14) (ℓ := 4) (h := 20) (κ' := 11) (ℓ' := 4) (h' := 19) (kq := 7) (t := 45) (c := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 2 starts from `mid2`'s candidate. -/
theorem rep_start18_2 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 7 - 1 + 4) Tc U)
    (hi : List E2) : RepT (d18 2) (candC (kap18 2) Tc hi) (Lvm6.Whir.mid2.L.cand hi U) :=
  rep_cand (ko := 10) (ℓ := 4) (h := 19) (κ' := 7) (ℓ' := 4) (h' := 18) (kq := 4) (t := 28) (c := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- Level 3 starts from `mid3`'s candidate. -/
theorem rep_start18_3 {Tc : CT E2 (0 + 4)} {U : Lvm6.Whir.Tup E2 (0 + 4)} (hR : RepT (2 ^ 3 - 1 + 4) Tc U)
    (hi : List E2) : RepT (d18 3) (candC (kap18 3) Tc hi) (Lvm6.Whir.mid3.L.cand hi U) :=
  rep_cand (ko := 6) (ℓ := 4) (h := 18) (κ' := 3) (ℓ' := 4) (h' := 17) (kq := 2) (t := 21) (c := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR hi

/-- **Level 4 starts from W1's final polynomial**: its coefficients are `s`. -/
theorem rep_start18_4 (s : List E2) : RepT (d18 4) (fun _ x ↦ s.getD x 0) (Lvm6.Whir.fin18.Fv.fpoly s) :=
  rep_fpoly (κ := 3) (ℓ := 4) (by norm_num) (by norm_num) s

end W1

end Lvm6.X
