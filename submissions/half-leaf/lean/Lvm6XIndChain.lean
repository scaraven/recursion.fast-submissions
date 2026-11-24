-- lvm6 EXI: the descent's five levels chained against the opening's facts at `P18`. Per level, `levelX_back` with
-- the level's start tuple (final level: the final polynomial; mid level: `cand hi U` of the next level's tuple `U`,
-- whose `StartOK` comes from `TailFacts` as in `lvBack_of_open`); across levels, the machine's inputs (`LvRun`: the
-- front's words and challenges in the round tables, the glue's start columns) are tied to the opening's log by
-- `Mach` (the EXF/EXG facts, a hypothesis here). New.
import Lvm6XInd

/-!
# The five levels

* **`LvRun`**: a level's machine inputs after its transition (layout, `TblOK` for the rounds `rs`, the start
  columns representing `Tc`, `Inv`, no output). **`RepAt M L d U`**: the level's columns in `M` represent `U`.
* **`levelX_run`**: `levelX_back` from `LvRun`. **`h3_of_round`**: W1's `RoundOK` gives `d + 3 ≤ A` per round.
* **`fin_step`** / **`mid_step`**: one level of the ladder on the machine, from the opening's facts of that level.
* **`RunMid`**, **`RunFin`**: the log runs of a level's pieces (the witnesses `OpenSem` names); **`GlueIn`**,
  **`FinIn`**: the machine's inputs of a level for those witnesses; **`Mach`**: all five, for every decomposition
  of the opening's log (`lvRun`: the state after the first `j` levels of `descX6`).
* **`chainD`**: from `OpenSem` at `ladD` and `Mach`, the descent's level-0 columns represent a level-0 tuple of
  the list satisfying the claim (`Back`'s facts), with `Inv` and the front's output.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open LeanVM.Protocol.Compile (Ev)
open scoped ENNReal

/-! ## A level from its machine inputs -/

/-- **A level's machine inputs** at state `s`: the level's numbers, the transition's `Inv` and output, the layout,
the round tables of the rounds `rs` on the level's word `Q`, the start columns representing `Tc`. -/
structure LvRun (I : Array Word) (i : ℕ) (L : LevelX) (s : St) (h d tb tS m J : ℕ) (nc : ℕ → ℕ) (nO lo : ℕ)
    (dom : Fin (2 ^ h) ↪ E2) (rs : List (Rnd E2)) (Q : Wd E2 (2 ^ h) (m + J)) (Tc : CT E2 m) : Prop where
  hh : ht6 i = h
  hN64 : ht6 i + 1 ≤ 64
  hNN : (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i
  hB : regs ≤ L.B
  hE : fdEnd L.B (ht6 i) < 2 ^ 64
  hd : d + 3 ≤ 2 ^ ht6 i
  hcol : fdEnd L.B (ht6 i) ≤ L.colB
  hstr : 2 ^ ht6 i ≤ L.str
  htb : regs ≤ tb
  htS : regs ≤ tS
  htr : Inv (semXIR I L.tr s).M
  hO : (semXIR I L.tr s).o = s.o
  hlay : (∀ r < J, (sbList (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) d tS r (colsL (semXIR I L.tr s).M (ht6 i + 1)
      (ht6 i) d tb tS (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) r)).length = d + 3) →
    GrpsOK (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS
      (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) nc (semXIR I L.tr s).M.size L.gs 0
  hJ : (L.gs.map GroupX.nr).sum = J
  hnc : nO ≤ nc J
  hT : TblOK (semXIR I L.tr s).M h tb tS dom m J (rs.map fun r ↦ (r.α, r.β)) Q
  hC : ColsRep d (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) Tc
  hlo : lo ≤ L.B
  hfr : ∀ x, regs ≤ x → x < lo → rd (semXIR I L.tr s).M x = rd s.M x

/-- **The level's first `n` columns in `M` represent `U`** (`d + 1` coefficients a column). -/
def RepAt (M : Mem) (L : LevelX) (d n : ℕ) {m : ℕ} (U : Tup E2 m) : Prop :=
  ∃ Tc : CT E2 m, RepT d Tc U ∧ ColsRepN d n (fun q x ↦ rdK M (L.colB + L.str * q + x)) Tc

/-- **`levelX_back` from the machine inputs.** -/
theorem levelX_run (I : Array Word) (i : ℕ) (L : LevelX) (s : St) {h d tb tS m J : ℕ} {nc : ℕ → ℕ} {nO lo : ℕ}
    {dom : Fin (2 ^ h) ↪ E2} (hdom : ∀ j, dom j = algebraMap BF64 E2 (ptK j)) {rs : List (Rnd E2)}
    {Q : Wd E2 (2 ^ h) (m + J)} {Tc : CT E2 m} (H : LvRun I i L s h d tb tS m J nc nO lo dom rs Q Tc)
    {Ar : ℕ → ℕ} {t : ℕ} {W : Tup E2 (m + J) →ₗ[E2] E2} {σ : E2} {a : ℕ}
    (hG : GoodRs dom Ar d J t rs Q W σ) (hch : ∀ s, t ≤ s → s + 1 < t + J → Ar s ≤ Ar (s + 1) - 1)
    (ha : 0 < J → a ≤ Ar t - 1) (h3 : ∀ s, t ≤ s → s < t + J → d + 3 ≤ Ar s) {P : Tup E2 m}
    (hR : RepT d Tc P) (hP : DegLE d P) (hA : aOut Ar a t J ≤ (agree dom P (foldsQ dom J rs Q)).card)
    (hW : foldsW J rs W P = foldsC J rs σ) :
    ∃ T : Tup E2 (m + J), DegLE d T ∧ a ≤ (agree dom T Q).card ∧ W T = σ ∧
      RepAt (semXIR I (levelX i L) s).M L d nO T ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = s.o ∧
      ∀ x, regs ≤ x → x < lo → rd (semXIR I (levelX i L) s).M x = rd s.M x := by
  obtain ⟨T, Tc', h1, h2, h3', h4, h5, h6, h7, h8⟩ := levelX_back I i L s nc H.hh hdom H.hN64 H.hB H.hE H.hNN H.hd
    H.hcol H.hstr H.htb H.htS H.htr H.hlay H.hJ rs Q H.hT hG hch ha h3 H.hC hR hP hA hW
  exact ⟨T, h2, h3', h4, ⟨Tc', h1, h5.mono H.hnc⟩, h6, h7.trans H.hO, fun x hx hlo ↦
    (h8 x hx (lt_of_lt_of_le hlo H.hlo)).trans (H.hfr x hx hlo)⟩

/-- **A round's threshold exceeds `d + 2`** (W1's `RoundOK`: `n·d < (A − 1)²`, with `1 ≤ d`, `d + 3 ≤ n`). -/
theorem h3_of_round {n d A : ℕ} (h : n * d < (A - 1) * (A - 1)) (hd : 1 ≤ d) (hn : d + 3 ≤ n) : d + 3 ≤ A := by
  by_contra hc
  have h1 : A - 1 ≤ d + 1 := by omega
  have h2 : (A - 1) * (A - 1) ≤ (d + 1) * (d + 1) := Nat.mul_self_le_mul_self h1
  have h4 : (d + 1) * (d + 1) ≤ n * d := by nlinarith
  omega

section Steps

variable {WI : WtIface E2} {I' : ChalIface E2} {εmax : ℝ≥0∞}

/-- **The final level on the machine**: from the level's opening facts (rounds, final polynomial `fpoly sc`) and
the machine's inputs with start columns representing `fpoly sc`. -/
theorem fin_step (I : Array Word) (i : ℕ) (L : LevelX) (s : St) {h ℓ nO lo : ℕ} (V : FinLv E2 WI (2 ^ h) ℓ) {a : ℕ}
    (hok : FinOK I' εmax V a) (hdom : ∀ j, V.Fv.dom j = algebraMap BF64 E2 (ptK j)) (hd1 : 1 ≤ V.Fv.d)
    (w : WI.Wt (0 + ℓ)) (σ : E2) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (hw : V.WOK w) (rs : List (Rnd E2)) (sc : List E2)
    (hG : GoodRs V.Fv.dom (fun t ↦ (V.par t).A) V.Fv.d ℓ V.t₀ rs (V.word (cs.take (V.i + 1))) (WI.den w) σ)
    (hA : aOut (fun t ↦ (V.par t).A) a V.t₀ ℓ ≤
      (agree V.Fv.dom (V.Fv.fpoly sc) (foldsQ V.Fv.dom ℓ rs (V.word (cs.take (V.i + 1))))).card)
    (hC : V.WOK w → WI.den (wFolds WI ℓ rs w) (V.Fv.fpoly sc) = foldsC ℓ rs σ)
    (hM : ∃ tb tS nc Tc, RepT V.Fv.d Tc (V.Fv.fpoly sc) ∧
      LvRun I i L s h V.Fv.d tb tS 0 ℓ nc nO lo V.Fv.dom rs (V.word (cs.take (V.i + 1))) Tc) :
    ∃ U : Tup E2 (0 + ℓ), DegLE V.Fv.d U ∧ a ≤ (agree V.Fv.dom U (V.word (cs.take (V.i + 1)))).card ∧
      WI.den w U = σ ∧ RepAt (semXIR I (levelX i L) s).M L V.Fv.d nO U ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = s.o ∧
      ∀ x, regs ≤ x → x < lo → rd (semXIR I (levelX i L) s).M x = rd s.M x := by
  obtain ⟨tb, tS, nc, Tc, hR, H⟩ := hM
  have hC' := hC hw
  rw [den_wFolds] at hC'
  exact levelX_run I i L s hdom H hG hok.hchain hok.ha
    (fun t h1 h2 ↦ h3_of_round (hok.hpar t h1 h2).1 hd1 (H.hh ▸ H.hd)) hR (V.Fv.fdeg sc) hA hC'

/-- **A mid level on the machine**: from the level's opening facts (rounds, `TailFacts` of the tail `o`), a tuple
`U` of the next level satisfying the next claim, and the machine's inputs with start columns representing
`cand o.hi U`. -/
theorem mid_step (I : Array Word) (i : ℕ) (L : LevelX) (s : St) {h ℓ n' ℓ' nO lo : ℕ}
    (M : MidLv E2 WI (2 ^ h) ℓ n' ℓ') (rest : Lad E2 WI n' ℓ') {a : ℕ}
    (hok : MidOK I' εmax M a rest.i rest.dom rest.d rest.WOK) (hdom : ∀ j, M.L.dom j = algebraMap BF64 E2 (ptK j))
    (hd1 : 1 ≤ M.L.d) (w : WI.Wt (0 + ℓ)) (σ : E2) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (hw : M.WOK w)
    (rs : List (Rnd E2)) (o : TailOut E2 M.L.ko M.L.t (2 ^ h))
    (hG : GoodRs M.L.dom (fun t ↦ (M.par t).A) M.L.d ℓ M.t₀ rs (M.word (cs.take (M.i + 1))) (WI.den w) σ)
    (htf : TailFacts M.L (foldsQ M.L.dom ℓ rs (M.word (cs.take (M.i + 1)))) (rest.word (cs.take (M.i + 2)))
      (WI.den (wFolds WI ℓ rs w)) (foldsC ℓ rs σ) (aOut (fun t ↦ (M.par t).A) a M.t₀ ℓ) M.A' o)
    (U : Tup E2 (0 + ℓ')) (hU : DegLE rest.d U)
    (hUa : M.A' ≤ (agree rest.dom U (rest.word (cs.take (rest.i + 1)))).card)
    (hUw : WI.den (M.wGlue (wFolds WI ℓ rs w) o) U = gluedC (foldsC ℓ rs σ) o.y o.lam o.c)
    (hM : ∃ tb tS nc Tc, RepT M.L.d Tc (M.L.cand o.hi U) ∧
      LvRun I i L s h M.L.d tb tS 0 ℓ nc nO lo M.L.dom rs (M.word (cs.take (M.i + 1))) Tc) :
    ∃ U₀ : Tup E2 (0 + ℓ), DegLE M.L.d U₀ ∧ a ≤ (agree M.L.dom U₀ (M.word (cs.take (M.i + 1)))).card ∧
      WI.den w U₀ = σ ∧ RepAt (semXIR I (levelX i L) s).M L M.L.d nO U₀ ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = s.o ∧
      ∀ x, regs ≤ x → x < lo → rd (semXIR I (levelX i L) s).M x = rd s.M x := by
  obtain ⟨-, htb, hc⟩ := htf
  rw [hok.den_wGlue w hw rs o, hc] at hUw
  have hi : rest.i + 1 = M.i + 2 := by rw [hok.hi']
  rw [hi, hok.hdom'] at hUa
  rw [hok.hd'] at hU
  obtain ⟨hq, hA⟩ := htb U ((mem_tupleList _ _ _ _ _).mpr ⟨hU, hUa⟩) hUw
  have hq0 := congrFun hq 0
  simp only [coefQ, Fin.cons_zero, Pi.zero_apply] at hq0
  have hWc : WI.den (wFolds WI ℓ rs w) (M.L.cand o.hi U) = foldsC ℓ rs σ := by
    rw [TailIface.cand, map_add, hok.hWH w hw rs o.hi, add_zero]
    exact sub_eq_zero.mp hq0
  rw [den_wFolds] at hWc
  obtain ⟨tb, tS, nc, Tc, hR, H⟩ := hM
  exact levelX_run I i L s hdom H hG hok.hchain hok.ha
    (fun t h1 h2 ↦ h3_of_round (hok.hpar t h1 h2).1 hd1 (H.hh ▸ H.hd)) hR (M.L.cand_deg U o.hi hU) hA hWc

end Steps

/-! ## The machine's inputs, tied to the opening's log -/

/-- **A mid level's runs** on the log `l`: the rounds return `rs`, the tail returns `o`, the rest is `l'`. -/
def RunMid {n ℓ n' ℓ' : ℕ} (M : MidLv E2 WtE n ℓ n' ℓ') (l : List Ev) (rs : List (Rnd E2))
    (o : TailOut E2 M.L.ko M.L.t n) (l' : List Ev) : Prop :=
  ∃ l₁ l₃, l = l₁ ++ (l₃ ++ l') ∧ (roundsP chalE2 M.g ℓ).after l₁ = some (.ret rs) ∧
    (tailP M.L chalE2 M.ht M.wd M.i M.gO M.gQ (M.vals rs)).after l₃ = some (.ret o)

/-- **The final level's runs** on the log `l`: the rounds return `rs`, the final scalars are `sc`. -/
def RunFin {n ℓ : ℕ} (V : FinLv E2 WtE n ℓ) (l : List Ev) (rs : List (Rnd E2)) (sc : List E2) : Prop :=
  ∃ l₁ l₃ l₄, l = l₁ ++ (l₃ ++ l₄) ∧ (roundsP chalE2 V.g ℓ).after l₁ = some (.ret rs) ∧
    (readFs chalE2 V.Fv.nf).after l₃ = some (.ret sc)

/-- **The heap below `b` is the front's**: `s` agrees with `s₀` on `[regs, b)`. -/
def Agree (s₀ s : St) (b : ℕ) : Prop := ∀ x, regs ≤ x → x < b → rd s.M x = rd s₀.M x

/-- **A mid level's machine inputs** at state `s` (after the next level `Lp`) for the rounds `rs` and the tail `o`:
for every tuple `U` the next level's first `nP` columns represent (degree `d'`), if the heap below `b` is still the
front's (`s₀`) and `Inv` holds, the level's transition (with the glue) starts from columns representing `cand o.hi U` and keeps the
heap below `lo`. -/
def GlueIn (I : Array Word) (k : ℕ) (L Lp : LevelX) (s₀ : St) (b lo : ℕ) (s : St) {h ℓ n' ℓ' : ℕ}
    (M : MidLv E2 WtE (2 ^ h) ℓ n' ℓ') (d' nP nO : ℕ) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word))
    (rs : List (Rnd E2)) (o : TailOut E2 M.L.ko M.L.t (2 ^ h)) : Prop :=
  ∀ U : Tup E2 (0 + ℓ'), RepAt s.M Lp d' nP U → Agree s₀ s b → Inv s.M → ∃ tb tS nc Tc, RepT M.L.d Tc (M.L.cand o.hi U) ∧
    LvRun I k L s h M.L.d tb tS 0 ℓ nc nO lo M.L.dom rs (M.word (cs.take (M.i + 1))) Tc

/-- **The final level's machine inputs** at state `s` for the rounds `rs` and the final scalars `sc`. -/
def FinIn (I : Array Word) (k : ℕ) (L : LevelX) (lo : ℕ) (s : St) {h ℓ : ℕ} (V : FinLv E2 WtE (2 ^ h) ℓ) (nO : ℕ)
    (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (rs : List (Rnd E2)) (sc : List E2) : Prop :=
  ∃ tb tS nc Tc, RepT V.Fv.d Tc (V.Fv.fpoly sc) ∧
    LvRun I k L s h V.Fv.d tb tS 0 ℓ nc nO lo V.Fv.dom rs (V.word (cs.take (V.i + 1))) Tc

/-- **The state after the first `j` levels** of `descX6` (levels `4, …, 5 − j`). -/
def lvRun (I : Array Word) (Lv : ℕ → LevelX) (s₀ : St) : ℕ → St
  | 0 => s₀
  | j + 1 => semXIR I (levelX (4 - j) (Lv (4 - j))) (lvRun I Lv s₀ j)

/-- **The descent's machine inputs at `P18`** (the front's words and challenges, the levels and their glue): for
every decomposition of the opening's log `l` into the levels' runs, each level's inputs at the state the levels below
leave, given that the heap below `b` is still the front's; levels 4–1 keep the heap below `b`, level 0 leaves `n₀`
columns. -/
def Mach (I : Array Word) (Lv : ℕ → LevelX) (n₀ b : ℕ) (s₀ : St)
    (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (l : List Ev) : Prop :=
  ∀ rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc,
    RunMid mid0 l rs0 o0 l1 → RunMid mid1 l1 rs1 o1 l2 → RunMid mid2 l2 rs2 o2 l3 → RunMid mid3 l3 rs3 o3 l4 →
    RunFin finD l4 rs4 sc →
    FinIn I 4 (Lv 4) b (lvRun I Lv s₀ 0) finD (2 * 2 ^ 4) cs rs4 sc ∧
    GlueIn I 3 (Lv 3) (Lv 4) s₀ b b (lvRun I Lv s₀ 1) mid3 finD.Fv.d (2 * 2 ^ 4) (2 * 2 ^ 4) cs rs3 o3 ∧
    GlueIn I 2 (Lv 2) (Lv 3) s₀ b b (lvRun I Lv s₀ 2) mid2 mid3.L.d (2 * 2 ^ 4) (2 * 2 ^ 4) cs rs2 o2 ∧
    GlueIn I 1 (Lv 1) (Lv 2) s₀ b b (lvRun I Lv s₀ 3) mid1 mid2.L.d (2 * 2 ^ 4) (2 * 2 ^ 4) cs rs1 o1 ∧
    GlueIn I 0 (Lv 0) (Lv 1) s₀ b 0 (lvRun I Lv s₀ 4) mid0 mid1.L.d (2 * 2 ^ 4) n₀ cs rs0 o0

theorem Agree.step {s₀ s s' : St} {b : ℕ} (h : Agree s₀ s b)
    (hf : ∀ x, regs ≤ x → x < b → rd s'.M x = rd s.M x) : Agree s₀ s' b :=
  fun x hx hb ↦ (hf x hx hb).trans (h x hx hb)

/-! ## The chain -/

/-- **The five levels chained at `P17`** (PORT17 X1, W1's ladder): from the opening's facts for a multiaffine claim and the machine's inputs
tied to the opening's log, after level 0 the first `n₀` columns represent a level-0 tuple of degree `≤ 2^18 + 5`
agreeing with commitment 0's word on `526,650` columns and satisfying the claim (`Back`'s facts), with `Inv` and
the output of the state before the descent. -/
theorem chainD (I : Array Word) (Lv : ℕ → LevelX) (n₀ b : ℕ) (s₀ : St) (cl : StackClaim6)
    (hma : cl.Multiaffine 24) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (l : List Ev)
    (hs : OpenSem WtE chalE2 ladD (w₀ cl) cl.2 (526656 - 6) cs l) (hM : Mach I Lv n₀ b s₀ cs l) :
    ∃ U : Tup E2 (0 + 6), DegLE (2 ^ 18 - 1 + 6) U ∧
      526656 - 6 ≤ (agree (domE 20 (by norm_num)) U (wordE true 0 (0 + 6) 20 cs)).card ∧
      WtE.den (w₀ cl) U = cl.2 ∧ RepAt (lvRun I Lv s₀ 5).M (Lv 0) (2 ^ 18 - 1 + 6) n₀ U ∧
      Inv (lvRun I Lv s₀ 5).M ∧ (lvRun I Lv s₀ 5).o = s₀.o := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := ladD_ok
  have hw0 : mid0.WOK (w₀ cl) := ⟨rfl, MA_w₀ cl hma⟩
  obtain ⟨rs0, a0, b0, e0, hr0, hG0, o0, c0, l1, f0, ho0, htf0, hs1⟩ := hs
  obtain ⟨rs1, a1, b1, e1, hr1, hG1, o1, c1, l2, f1, ho1, htf1, hs2⟩ := hs1
  obtain ⟨rs2, a2, b2, e2, hr2, hG2, o2, c2, l3, f2, ho2, htf2, hs3⟩ := hs2
  obtain ⟨rs3, a3, b3, e3, hr3, hG3, o3, c3, l4, f3, ho3, htf3, hs4⟩ := hs3
  obtain ⟨rs4, a4, b4, e4, hr4, hG4, sc, c4, d4, f4, hsc, hA4, hC4⟩ := hs4
  obtain ⟨m4, m3, m2, m1, m0⟩ := hM rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc
    ⟨a0, c0, by rw [e0, f0], hr0, ho0⟩ ⟨a1, c1, by rw [e1, f1], hr1, ho1⟩ ⟨a2, c2, by rw [e2, f2], hr2, ho2⟩
    ⟨a3, c3, by rw [e3, f3], hr3, ho3⟩ ⟨a4, c4, d4, by rw [e4, f4], hr4, hsc⟩
  have hw1 := k0.hglue _ hw0 rs0 o0
  have hw2 := k1.hglue _ hw1 rs1 o1
  have hw3 := k2.hglue _ hw2 rs2 o2
  have hw4 := k3.hglue _ hw3 rs3 o3
  have g0 : Agree s₀ (lvRun I Lv s₀ 0) b := fun _ _ _ ↦ rfl
  obtain ⟨U4, hU4, hA4', hW4, hR4, hI4, hO4, hF4⟩ := fin_step I 4 (Lv 4) (lvRun I Lv s₀ 0) finD k4 (fun _ ↦ rfl)
    (by show 1 ≤ 2 ^ 2 - 1 + 4; norm_num) _ _ cs hw4 rs4 sc hG4 hA4 hC4 m4
  have g1 : Agree s₀ (lvRun I Lv s₀ 1) b := g0.step hF4
  obtain ⟨U3, hU3, hA3', hW3, hR3, hI3, hO3, hF3⟩ := mid_step I 3 (Lv 3) (lvRun I Lv s₀ 1) mid3 _ k3 (fun _ ↦ rfl)
    (by show 1 ≤ 2 ^ (5 + 1) - 1 + 4; norm_num) _ _ cs hw3 rs3 o3 hG3 htf3 U4 hU4 hA4' hW4 (m3 U4 hR4 g1 hI4)
  have g2 : Agree s₀ (lvRun I Lv s₀ 2) b := g1.step hF3
  obtain ⟨U2, hU2, hA2', hW2, hR2, hI2, hO2, hF2⟩ := mid_step I 2 (Lv 2) (lvRun I Lv s₀ 2) mid2 _ k2 (fun _ ↦ rfl)
    (by show 1 ≤ 2 ^ (9 + 1) - 1 + 4; norm_num) _ _ cs hw2 rs2 o2 hG2 htf2 U3 hU3 hA3' hW3 (m2 U3 hR3 g2 hI3)
  have g3 : Agree s₀ (lvRun I Lv s₀ 3) b := g2.step hF2
  obtain ⟨U1, hU1, hA1', hW1, hR1, hI1, hO1, hF1⟩ := mid_step I 1 (Lv 1) (lvRun I Lv s₀ 3) mid1 _ k1 (fun _ ↦ rfl)
    (by show 1 ≤ 2 ^ (13 + 1) - 1 + 4; norm_num) _ _ cs hw1 rs1 o1 hG1 htf1 U2 hU2 hA2' hW2 (m1 U2 hR2 g3 hI2)
  have g4 : Agree s₀ (lvRun I Lv s₀ 4) b := g3.step hF1
  obtain ⟨U0, hU0, hA0', hW0, hR0, hI0, hO0, -⟩ := mid_step I 0 (Lv 0) (lvRun I Lv s₀ 4) mid0 _ k0 (fun _ ↦ rfl)
    (by show 1 ≤ 2 ^ (17 + 1) - 1 + 6; norm_num) (w₀ cl) cl.2 cs hw0 rs0 o0 hG0 htf0 U1 hU1 hA1'
    hW1 (m0 U1 hR1 g4 hI1)
  have e : mid0.word (cs.take (mid0.i + 1)) = wordE true 0 (0 + 6) 20 cs := ladD_word_take cs
  rw [e] at hA0'
  exact ⟨U0, hU0, hA0', hW0, hR0, hI0, hO0.trans (hO1.trans (hO2.trans (hO3.trans hO4)))⟩

end Lvm6.X
