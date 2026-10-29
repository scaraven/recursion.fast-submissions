-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).
import FRVerifierImplNode4
import FRVIRTplMaskN

/-!
# The replay template of a node's `linkWAll` (`NI4.linkWAll4I ν`), gate for gate

One node kind's sub-template for the previous node's `linkWAll` (inputs `tt : AF a`, then
`rr : AF b`), mirroring `linkWAll4I ν tt rr` array for array:

* the eight `eq` tables (`tabsG`): `τ`'s and `r_blk`'s low 9 and high `nb − 9` coordinates (`bt`),
  `θ`'s and `r_pos`'s low 8 and high 2 (`tab10`);
* `Eθ` (256 products), `Eτ_σ` (2 × 498), `eq(r_blk, ·)` on the same WOTS blocks (2 × 498), `EP_σ`
  (2 × 498), `EM_σ` (2 × 146), each one product per entry from the tables (`BT.eq`, `eq10`);
* per family `f` (`famG`): the field weight `SW` and `MI` (3 products per field bit), `MS` (4), the
  two source sums `SW·Σ EP_σ` (2) and `Σ_t (Eτ_σ·EM_σ)·MS` (4 per source).

**`tplLW_ok`**: with `e.one = 1`, the inputs `tt ++ rr` and the gate equations, the outputs are
`linkWAll4I ν tt rr`. About 14.3 k products per kind (`N4`).
-/

namespace FR
namespace Tpl
open Circ Finset NI4 NT4

variable {e : Env}

/-! ## Generic pieces -/

/-- Output `i` of a stage of `n` products at locals `k …` (`[]` past it). -/
def pL (k n i : ℕ) : LinT := if i < n then L (k + i) else []

theorem pL_ev {k n : ℕ} {A B : ℕ → LinT} (h : Eqns e (mulsG n A B) k) (i : ℕ) :
    (pL k n i).ev e = if i < n then (A i).ev e * (B i).ev e else 0 := by
  unfold pL; split_ifs with hi
  · rw [ev_L, mulsG_eqns h i hi]
  · rfl

/-- **Tables one after the other** from local `k`: their gates and their entries. -/
def tabsG : List (List LinT) → ℕ → List Gate × List (List LinT)
  | [], _ => ([], [])
  | cs :: css, k =>
    let T := eqTblG cs k
    let r := tabsG css (k + nlocs T.1)
    (T.1 ++ r.1, T.2 :: r.2)

theorem tabsG_ev (h1 : e.one = 1) : ∀ (css : List (List LinT)) (k : ℕ), Eqns e (tabsG css k).1 k →
    ∀ j < css.length, ∀ i,
      (((tabsG css k).2.getD j []).getD i []).ev e = (eqTable ((css.getD j []).map (LinT.ev e))).getD i 0
  | [], _, _, j, hj, i => absurd hj (by simp)
  | cs :: css, k, h, j, hj, i => by
    simp only [tabsG, Eqns.append] at h
    rcases j with _ | j
    · simp only [tabsG, List.getD_cons_zero]
      exact tblG_ent h1 h.1 i
    · simp only [tabsG, List.getD_cons_succ]
      exact tabsG_ev h1 css _ h.2 j (by simpa using hj) i

/-- A sum of forms over `i < n`. -/
def sumG (n : ℕ) (g : ℕ → LinT) : LinT := (List.range n).flatMap g

theorem sumG_ev (n : ℕ) (g : ℕ → LinT) : (sumG n g).ev e = ∑ i ∈ range n, (g i).ev e := by
  rw [sumG, ev_flatMap, sum_range_list (M := F)]

theorem ofFn_getD {n : ℕ} (g : Fin n → F) (c : ℕ) :
    (Array.ofFn g).getD c 0 = if h : c < n then g ⟨c, h⟩ else 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]; split_ifs <;> rfl

theorem sum_two_mul {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (g : ℕ → M) :
    ∑ i ∈ range (2 * n), g i = ∑ σ ∈ range 2, ∑ t ∈ range n, g (σ * n + t) := by
  rw [two_mul, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  simp only [zero_mul, zero_add, one_mul]

/-! ## One family -/

section Fam
variable (eθ pA pB : ℕ → LinT) (eτ ep em : ℕ → ℕ → LinT)

/-- **Family `f`'s weight**, gate for gate (`linkWOneF`), its locals from `k`. -/
def famG (f k : ℕ) : List Gate × LinT :=
  let Lb := NodeT.fbits f
  let n := (NodeT.fam f).n
  let k3 := k + 3 * Lb
  let SW := sumG Lb fun s => L (k + Lb + s)
  let MI := sumG Lb fun s => L (k + 2 * Lb + s)
  (mulsG Lb (fun s => pA (NodeT.fpos f s % 256)) (fun s => pB (NodeT.fpos f s / 256 % 4)) ++
    (mulsG Lb eθ (fun s => L (k + s)) ++
    (mulsG Lb eθ (fun s => pA ((NodeT.fam f).mbo + s)) ++
    (mulsG 4 pB (fun _ => MI) ++
    (mulsG 2 (fun _ => SW) (fun σ => sumG n fun t => ep σ ((NodeT.fam f).src t)) ++
    (mulsG (2 * n) (fun i => eτ (i / n) ((NodeT.fam f).src (i % n)))
      (fun i => em (i / n) ((NodeT.fam f).mir (i % n) / 4)) ++
    mulsG (2 * n) (fun i => L (k3 + 6 + i)) (fun i => pL k3 4 ((NodeT.fam f).mir (i % n) % 4))))))),
   L (k3 + 4) ++ L (k3 + 5) ++ sc (-1) (sumG (2 * n) fun i => L (k3 + 6 + 2 * n + i)))

theorem famG_nlocs (f k : ℕ) :
    nlocs (famG eθ pA pB eτ ep em f k).1 = 3 * NodeT.fbits f + 6 + 4 * (NodeT.fam f).n := by
  simp only [famG, nlocs_append, mulsG_nlocs]; ring

variable {eθ pA pB eτ ep em} {EP Eτ EM : ℕ → Array F} {Pr : Array F × Array F} {Eθ : Array F}

set_option maxHeartbeats 1000000 in
/-- **`famG` computes `linkWOneF`.** -/
theorem famG_ev (h1 : e.one = 1) (f k : ℕ) (hn : 0 < (NodeT.fam f).n)
    (heθ : ∀ s, (eθ s).ev e = Eθ.getD s 0) (hpA : ∀ i, (pA i).ev e = Pr.1.getD i 0)
    (hpB : ∀ i, (pB i).ev e = Pr.2.getD i 0)
    (heτ : ∀ σ < 2, ∀ o, (eτ σ o).ev e = (Eτ σ).getD o 0)
    (hep : ∀ σ < 2, ∀ o, (ep σ o).ev e = (EP σ).getD o 0)
    (hem : ∀ σ < 2, ∀ o, (em σ o).ev e = (EM σ).getD o 0)
    (h : Eqns e (famG eθ pA pB eτ ep em f k).1 k) :
    (famG eθ pA pB eτ ep em f k).2.ev e = linkWOneF EP Eτ EM Pr Eθ f := by
  simp only [famG] at h ⊢
  simp only [Eqns.append, mulsG_nlocs] at h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h
  have e1 := mulsG_eqns g1
  have e2 := mulsG_eqns g2
  have e3 := mulsG_eqns g3
  have e4 := mulsG_eqns g4
  have e5 := mulsG_eqns g5
  have e6 := mulsG_eqns g6
  have e7 := mulsG_eqns g7
  set Lb := NodeT.fbits f
  set n := (NodeT.fam f).n
  -- SW, MI
  have hSW : (sumG Lb fun s => L (k + Lb + s)).ev e =
      sumTo Lb fun s => Eθ.getD s 0 * NodeI.eq10 Pr (NodeT.fpos f s) := by
    rw [sumG_ev, sumTo_eq]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs := Finset.mem_range.1 hs
    rw [ev_L, e2 s hs, heθ, ev_L, e1 s hs, hpA, hpB]; rfl
  have hMI : (sumG Lb fun s => L (k + 2 * Lb + s)).ev e =
      sumTo Lb fun s => Eθ.getD s 0 * Pr.1.getD ((NodeT.fam f).mbo + s) 0 := by
    rw [sumG_ev, sumTo_eq]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs := Finset.mem_range.1 hs
    rw [show k + Lb + Lb = k + 2 * Lb by ring] at e3
    rw [ev_L, e3 s hs, heθ, hpA]
  -- MS
  have hMS : ∀ c, (pL (k + 3 * Lb) 4 c).ev e = (Array.ofFn (n := 4) fun c =>
      Pr.2.getD c 0 * sumTo Lb fun s => Eθ.getD s 0 * Pr.1.getD ((NodeT.fam f).mbo + s) 0).getD c 0 := by
    intro c
    rw [show k + Lb + Lb + Lb = k + 3 * Lb by ring] at e4
    unfold pL
    split_ifs with hc
    · rw [ev_L, e4 c hc, hpB, hMI, ofFn_getD, dif_pos hc]
    · rw [ofFn_getD, dif_neg hc]; rfl
  -- the output
  rw [show k + Lb + Lb + Lb + 4 = k + 3 * Lb + 4 by ring] at e5
  rw [show k + Lb + Lb + Lb + 4 + 2 = k + 3 * Lb + 6 by ring] at e6
  rw [show k + Lb + Lb + Lb + 4 + 2 + 2 * n = k + 3 * Lb + 6 + 2 * n by ring] at e7
  simp only [ev_append, ev_sc, ev_L, sumG_ev]
  rw [e5 0 (by norm_num), e5 1 (by norm_num)]
  have hdiv : ∀ σ < 2, ∀ t < n, (σ * n + t) / n = σ ∧ (σ * n + t) % n = t := fun σ _ t ht => by
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  rw [Finset.sum_congr rfl fun i hi => by rw [e7 i (Finset.mem_range.1 hi), ev_L, e6 i (Finset.mem_range.1 hi)],
    sum_two_mul n hn]
  rw [Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun t ht => by
    obtain ⟨hd, hm⟩ := hdiv σ (Finset.mem_range.1 hσ) t (Finset.mem_range.1 ht)
    rw [hd, hm, heτ σ (Finset.mem_range.1 hσ), hem σ (Finset.mem_range.1 hσ), hMS]]
  simp only [sumG_ev, hSW]
  rw [Finset.sum_congr rfl fun t _ => hep 0 (by norm_num) _, Finset.sum_congr rfl fun t _ => hep 1 (by norm_num) _]
  unfold linkWOneF
  dsimp only
  rw [sumTo_eq 2, show NodeT.fbits f = Lb from rfl, show (NodeT.fam f).n = n from rfl]
  simp only [sumTo_eq n, Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

end Fam

/-! ## The node kind's template -/

section LW
variable (ν : Rev4.NodeKind) (a b : ℕ)

/-- The eight tables' coordinate forms (`tt` on inputs `0 … a−1`, `rr` on `a … a+b−1`). -/
def lwCs : List (List LinT) :=
  [(List.range 9).map (cT a), (List.range (nbN ν - 9)).map fun l => cT a (9 + l),
   (List.range 9).map (cR a b), (List.range (nbN ν - 9)).map fun l => cR a b (9 + l),
   (List.range 8).map fun l => cT a (nbN ν + l), (List.range 2).map fun l => cT a (nbN ν + (8 + l)),
   (List.range 8).map fun l => cR a b (nbN ν + l), (List.range 2).map fun l => cR a b (nbN ν + (8 + l))]

/-- The tables' gates and entries. -/
def lwT : List Gate × List (List LinT) := tabsG (lwCs ν a b) 0

/-- Entry `i` of table `j`. -/
def lwE (j i : ℕ) : LinT := ((lwT ν a b).2.getD j []).getD i []

/-- The stages' first locals. -/
def lwK8 : ℕ := nlocs (lwT ν a b).1
def lwK9 : ℕ := lwK8 ν a b + 256
def lwK10 : ℕ := lwK9 ν a b + 996
def lwK11 : ℕ := lwK10 ν a b + 996
def lwK12 : ℕ := lwK11 ν a b + 996
def lwK13 : ℕ := lwK12 ν a b + 292

/-- The WOTS block of product `i < 996` (slot `i / 498`) and the `WM` block of `i < 292`. -/
def xw (i : ℕ) : ℕ := N4c.wotsB ν (i / 498) + i % 498
def ym (i : ℕ) : ℕ := N4c.wmB ν (i / 146) + i % 146

/-- The accessors of the per-block arrays. -/
def lwEθ (s : ℕ) : LinT := pL (lwK8 ν a b) 256 s
def lwEτ (σ o : ℕ) : LinT := if σ < 2 ∧ o < 498 then L (lwK9 ν a b + (498 * σ + o)) else []
def lwEP (σ o : ℕ) : LinT := if σ < 2 ∧ o < 498 then L (lwK11 ν a b + (498 * σ + o)) else []
def lwEM (σ o : ℕ) : LinT := if σ < 2 ∧ o < 146 then L (lwK12 ν a b + (146 * σ + o)) else []

/-- The eight families, one after the other. -/
def lwFams : List ℕ → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | f :: fs, k =>
    let F := famG (lwEθ ν a b) (lwE ν a b 6) (lwE ν a b 7) (lwEτ ν a b) (lwEP ν a b) (lwEM ν a b) f k
    let r := lwFams fs (k + nlocs F.1)
    (F.1 ++ r.1, F.2 :: r.2)

/-- **The node kind `ν`'s `linkWAll` template** (inputs `tt : AF a`, then `rr : AF b`). -/
def tplLW : Tpl :=
  ⟨(lwT ν a b).1 ++
    (mulsG 256 (lwE ν a b 4) (fun _ => lwE ν a b 5 0) ++
    (mulsG 996 (fun i => lwE ν a b 0 (xw ν i % 512)) (fun i => lwE ν a b 1 (xw ν i / 512)) ++
    (mulsG 996 (fun i => lwE ν a b 2 (xw ν i % 512)) (fun i => lwE ν a b 3 (xw ν i / 512)) ++
    (mulsG 996 (fun i => L (lwK9 ν a b + i)) (fun i => L (lwK10 ν a b + i)) ++
    (mulsG 292 (fun i => lwE ν a b 2 (ym ν i % 512)) (fun i => lwE ν a b 3 (ym ν i / 512)) ++
    (lwFams ν a b (List.range nLinkFam) (lwK13 ν a b)).1))))),
   (lwFams ν a b (List.range nLinkFam) (lwK13 ν a b)).2⟩

end LW

theorem lwFams_len (ν : Rev4.NodeKind) (a b : ℕ) : ∀ (fs : List ℕ) (k : ℕ), (lwFams ν a b fs k).2.length = fs.length
  | [], _ => rfl
  | f :: fs, k => by simp [lwFams, lwFams_len ν a b fs]

theorem tplLW_outs (ν : Rev4.NodeKind) (a b : ℕ) : (tplLW ν a b).outs.length = nLinkFam := by
  simp [tplLW, lwFams_len]

/-! ## Correctness -/

theorem ofFn_eq_range {n : ℕ} (g : Fin n → F) (g' : ℕ → F) (hg : ∀ l : Fin n, g l = g' l) :
    List.ofFn g = (List.range n).map g' :=
  List.ext_getElem (by simp) fun i h1 _ => by simp [hg ⟨i, by simpa using h1⟩]

theorem fam_pos {f : ℕ} (hf : f < nLinkFam) : 0 < (NodeT.fam f).n := by
  simp only [nLinkFam] at hf
  interval_cases f <;> decide

/-- **The families' outputs** (`famG_ev` along the list). -/
theorem lwFams_ev {ν : Rev4.NodeKind} {a b : ℕ} (h1 : e.one = 1) {EP Eτ EM : ℕ → Array F} {Pr : Array F × Array F} {Eθ : Array F}
    (heθ : ∀ s, (lwEθ ν a b s).ev e = Eθ.getD s 0)
    (hpA : ∀ i, (lwE ν a b 6 i).ev e = Pr.1.getD i 0)
    (hpB : ∀ i, (lwE ν a b 7 i).ev e = Pr.2.getD i 0)
    (heτ : ∀ σ < 2, ∀ o, (lwEτ ν a b σ o).ev e = (Eτ σ).getD o 0)
    (hep : ∀ σ < 2, ∀ o, (lwEP ν a b σ o).ev e = (EP σ).getD o 0)
    (hem : ∀ σ < 2, ∀ o, (lwEM ν a b σ o).ev e = (EM σ).getD o 0) :
    ∀ (fs : List ℕ) (k : ℕ), (∀ f ∈ fs, f < nLinkFam) → Eqns e (lwFams ν a b fs k).1 k →
    (lwFams ν a b fs k).2.map (LinT.ev e) = fs.map (linkWOneF EP Eτ EM Pr Eθ)
  | [], _, _, _ => rfl
  | f :: fs, k, hf, h => by
    simp only [lwFams, Eqns.append] at h
    simp only [lwFams, List.map_cons]
    rw [famG_ev h1 f k (fam_pos (hf f (List.mem_cons_self ..))) heθ hpA hpB heτ hep hem h.1,
      lwFams_ev h1 heθ hpA hpB heτ hep hem fs _ (fun g hg => hf g (List.mem_cons_of_mem _ hg)) h.2]

theorem bt_eq_mul (n : ℕ) (a : Array F) (x : ℕ) :
    (bt n a).eq x = (bt n a).A.getD (x % 512) 0 * (bt n a).B.getD (x / 512) 0 := rfl

theorem xw_split {σ o : ℕ} (hσ : σ < 2) (ho : o < 498) :
    (498 * σ + o) / 498 = σ ∧ (498 * σ + o) % 498 = o ∧ 498 * σ + o < 996 := by omega

theorem ym_split {σ o : ℕ} (hσ : σ < 2) (ho : o < 146) :
    (146 * σ + o) / 146 = σ ∧ (146 * σ + o) % 146 = o ∧ 146 * σ + o < 292 := by omega

/-! ## The arrays of `linkWAll4I` -/

def lwPθ (ν : Rev4.NodeKind) (tt : Array F) : Array F × Array F := NodeI.tab10 fun l => tt.getD (nbN ν + l) 0
def lwPr (ν : Rev4.NodeKind) (rr : Array F) : Array F × Array F := NodeI.tab10 fun l => rr.getD (nbN ν + l) 0
def lwEθA (ν : Rev4.NodeKind) (tt : Array F) : Array F := Array.ofFn (n := 256) fun s => NodeI.eq10 (lwPθ ν tt) s
def lwEτA (ν : Rev4.NodeKind) (tt : Array F) (σ : ℕ) : Array F :=
  Array.ofFn (n := 498) fun o => (bt (nbN ν) tt).eq (N4c.wotsB ν σ + o)
def lwEPA (ν : Rev4.NodeKind) (tt rr : Array F) (σ : ℕ) : Array F :=
  Array.ofFn (n := 498) fun o => (lwEτA ν tt σ).getD o 0 * (bt (nbN ν) rr).eq (N4c.wotsB ν σ + o)
def lwEMA (ν : Rev4.NodeKind) (rr : Array F) (σ : ℕ) : Array F :=
  Array.ofFn (n := 146) fun o => (bt (nbN ν) rr).eq (N4c.wmB ν σ + o)

/-- `linkWAll4I` over the named arrays (`rfl`). -/
theorem linkWAll4I_eq (ν : Rev4.NodeKind) (tt rr : Array F) : linkWAll4I ν tt rr = Array.ofFn (n := nLinkFam)
    fun f => linkWOneF (fun σ => if σ = 0 then lwEPA ν tt rr 0 else lwEPA ν tt rr 1)
      (fun σ => if σ = 0 then lwEτA ν tt 0 else lwEτA ν tt 1)
      (fun σ => if σ = 0 then lwEMA ν rr 0 else lwEMA ν rr 1) (lwPr ν rr) (lwEθA ν tt) f := rfl

/-- `linkWOneF` reads its per-slot arrays at slots `0`, `1` only. -/
theorem linkWOneF_congr {EP Eτ EM EP' Eτ' EM' : ℕ → Array F} (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ)
    (hP : ∀ σ < 2, EP σ = EP' σ) (hτ : ∀ σ < 2, Eτ σ = Eτ' σ) (hM : ∀ σ < 2, EM σ = EM' σ) :
    linkWOneF EP Eτ EM Pr Eθ f = linkWOneF EP' Eτ' EM' Pr Eθ f := by
  unfold linkWOneF
  dsimp only
  rw [sumTo_eq (M := F) 2, sumTo_eq (M := F) 2]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ := Finset.mem_range.1 hσ
  rw [hP σ hσ, hτ σ hσ, hM σ hσ]

/-- `linkWAll4I` over the named per-slot arrays. -/
theorem linkWAll4I_eq' (ν : Rev4.NodeKind) (tt rr : Array F) : linkWAll4I ν tt rr = Array.ofFn (n := nLinkFam)
    fun f => linkWOneF (lwEPA ν tt rr) (lwEτA ν tt) (lwEMA ν rr) (lwPr ν rr) (lwEθA ν tt) f := by
  rw [linkWAll4I_eq]
  refine congrArg (Array.ofFn (n := nLinkFam)) (funext fun f => ?_)
  refine linkWOneF_congr _ _ f ?_ ?_ ?_ <;> intro σ hσ <;>
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp only [↓reduceIte, one_ne_zero]

section Proof
variable {ν : Rev4.NodeKind} {tt rr : Array F} (hi : InpIs e (tt.toList ++ rr.toList))
include hi

/-- **The eight tables are `bt`'s and `tab10`'s.** -/
theorem lwE_ev (h1 : e.one = 1) (h : Eqns e (lwT ν tt.size rr.size).1 0) (i : ℕ) :
    (lwE ν tt.size rr.size 0 i).ev e = (bt (nbN ν) tt).A.getD i 0 ∧
    (lwE ν tt.size rr.size 1 i).ev e = (bt (nbN ν) tt).B.getD i 0 ∧
    (lwE ν tt.size rr.size 2 i).ev e = (bt (nbN ν) rr).A.getD i 0 ∧
    (lwE ν tt.size rr.size 3 i).ev e = (bt (nbN ν) rr).B.getD i 0 ∧
    (lwE ν tt.size rr.size 4 i).ev e = (NodeI.tab10 fun l => tt.getD (nbN ν + l) 0).1.getD i 0 ∧
    (lwE ν tt.size rr.size 5 i).ev e = (NodeI.tab10 fun l => tt.getD (nbN ν + l) 0).2.getD i 0 ∧
    (lwE ν tt.size rr.size 6 i).ev e = (NodeI.tab10 fun l => rr.getD (nbN ν + l) 0).1.getD i 0 ∧
    (lwE ν tt.size rr.size 7 i).ev e = (NodeI.tab10 fun l => rr.getD (nbN ν + l) 0).2.getD i 0 := by
  have ht := fun j hj => tabsG_ev h1 (lwCs ν tt.size rr.size) 0 h j hj
  simp only [lwE, lwT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ht _ (by simp [lwCs])] <;> congr 2 <;>
    simp only [lwCs, List.getD_cons_zero, List.getD_cons_succ, List.map_map, Function.comp_def,
      cT_ev hi, cR_ev hi] <;>
    exact (ofFn_eq_range _ _ fun l => rfl).symm

set_option maxHeartbeats 1000000 in
/-- **The node kind `ν`'s `linkWAll` template computes `linkWAll4I ν`.** -/
theorem tplLW_ok (h1 : e.one = 1) (h : Eqns e (tplLW ν tt.size rr.size).gates 0) :
    (tplLW ν tt.size rr.size).outs.map (LinT.ev e) = encV (.af (linkWAll4I ν tt rr)) := by
  simp only [tplLW, Eqns.append, mulsG_nlocs, zero_add] at h
  obtain ⟨hT, h9, h10, h11, h12, h13, hF⟩ := h
  have hE := lwE_ev hi h1 hT
  have h9' : Eqns e (mulsG 256 (lwE ν tt.size rr.size 4) fun _ => lwE ν tt.size rr.size 5 0)
    (lwK8 ν tt.size rr.size) := h9
  have e10 := mulsG_eqns (k := lwK9 ν tt.size rr.size) h10
  have e11 := mulsG_eqns (k := lwK10 ν tt.size rr.size) h11
  have e12 := mulsG_eqns (k := lwK11 ν tt.size rr.size) h12
  have e13 := mulsG_eqns (k := lwK12 ν tt.size rr.size) h13
  have hF' : Eqns e (lwFams ν tt.size rr.size (List.range nLinkFam) (lwK13 ν tt.size rr.size)).1
    (lwK13 ν tt.size rr.size) := hF
  rw [linkWAll4I_eq']
  simp only [encV, Array.toList_ofFn]
  rw [ofFn_eq_range _ _ fun f => rfl]
  refine lwFams_ev (ν := ν) (a := tt.size) (b := rr.size) (e := e)
    (EP := lwEPA ν tt rr) (Eτ := lwEτA ν tt) (EM := lwEMA ν rr) (Pr := lwPr ν rr) (Eθ := lwEθA ν tt)
    h1 ?_ (fun i => (hE i).2.2.2.2.2.2.1) (fun i => (hE i).2.2.2.2.2.2.2) ?_ ?_ ?_
    (List.range nLinkFam) (lwK13 ν tt.size rr.size) (fun f hf => List.mem_range.1 hf) hF'
  · intro s
    rw [lwEθ, pL_ev h9', lwEθA, ofFn_getD]
    split_ifs with hs
    · rw [(hE s).2.2.2.2.1, (hE 0).2.2.2.2.2.1, NodeI.eq10, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs]; rfl
    · rfl
  · intro σ hσ o
    unfold lwEτ
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := xw_split hσ ho.2
      rw [ev_L, e10 _ d3, (hE _).1, (hE _).2.1, xw, d1, d2, lwEτA, ofFn_getD, dif_pos ho.2, bt_eq_mul]
    · rw [lwEτA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl
  · intro σ hσ o
    unfold lwEP
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := xw_split hσ ho.2
      rw [ev_L, e12 _ d3, ev_L, ev_L, e10 _ d3, e11 _ d3, (hE _).1, (hE _).2.1, (hE _).2.2.1, (hE _).2.2.2.1,
        xw, d1, d2, lwEPA, ofFn_getD, dif_pos ho.2, lwEτA, ofFn_getD, dif_pos ho.2, bt_eq_mul, bt_eq_mul]
    · rw [lwEPA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl
  · intro σ hσ o
    unfold lwEM
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := ym_split hσ ho.2
      rw [ev_L, e13 _ d3, (hE _).2.2.1, (hE _).2.2.2.1, ym, d1, d2, lwEMA, ofFn_getD, dif_pos ho.2, bt_eq_mul]
    · rw [lwEMA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl

end Proof

end Tpl
end FR
