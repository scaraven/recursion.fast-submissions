-- G6: this module also holds the former modules `FRVIRTplRepLW`, `FRVerifierImplNode4T` (one section each, in import order).
import FRVerifierImplNode4
import FRVIRTplEval
import FRNodeTarget4C

section G6_FRVIRTplRepLW

-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).

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

/-- The stages' first locals (`k8`: the tables' local count). -/
def lwK8 : ℕ := nlocs (lwT ν a b).1

end LW

/-! ### The template over a context (REPF): the tables and their local count built once

`tplLW` builds its tables once (`let`) and reads them through `E`/`k8`; reading `lwE ν a b j i`
(which rebuilds the tables) per accessor made the process start take 216 s (C1b-RESULT §4.2). The
spec accessors (`lwE`, `lwK8`) are the context's at `mkLW` (`tplLW_eq`). -/

section LWg
variable (ν : Rev4.NodeKind) (E : ℕ → ℕ → LinT) (k8 : ℕ)

def lwK9g : ℕ := k8 + 256
def lwK10g : ℕ := lwK9g k8 + 996
def lwK11g : ℕ := lwK10g k8 + 996
def lwK12g : ℕ := lwK11g k8 + 996
def lwK13g : ℕ := lwK12g k8 + 292

/-- The WOTS block of product `i < 996` (slot `i / 498`) and the `WM` block of `i < 292`. -/
def xw (i : ℕ) : ℕ := N4c.wotsB ν (i / 498) + i % 498
def ym (i : ℕ) : ℕ := N4c.wmB ν (i / 146) + i % 146

/-- The accessors of the per-block arrays. -/
def lwEθg (s : ℕ) : LinT := pL k8 256 s
def lwEτg (σ o : ℕ) : LinT := if σ < 2 ∧ o < 498 then L (lwK9g k8 + (498 * σ + o)) else []
def lwEPg (σ o : ℕ) : LinT := if σ < 2 ∧ o < 498 then L (lwK11g k8 + (498 * σ + o)) else []
def lwEMg (σ o : ℕ) : LinT := if σ < 2 ∧ o < 146 then L (lwK12g k8 + (146 * σ + o)) else []

/-- The eight families, one after the other. -/
def lwFamsg : List ℕ → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | f :: fs, k =>
    let F := famG (lwEθg k8) (E 6) (E 7) (lwEτg k8) (lwEPg k8) (lwEMg k8) f k
    let r := lwFamsg fs (k + nlocs F.1)
    (F.1 ++ r.1, F.2 :: r.2)

/-- **The template over a context**: the tables' gates `gT` (entries `E`, `k8` locals). -/
def tplLWg (gT : List Gate) : Tpl :=
  ⟨gT ++
    (mulsG 256 (E 4) (fun _ => E 5 0) ++
    (mulsG 996 (fun i => E 0 (xw ν i % 512)) (fun i => E 1 (xw ν i / 512)) ++
    (mulsG 996 (fun i => E 2 (xw ν i % 512)) (fun i => E 3 (xw ν i / 512)) ++
    (mulsG 996 (fun i => L (lwK9g k8 + i)) (fun i => L (lwK10g k8 + i)) ++
    (mulsG 292 (fun i => E 2 (ym ν i % 512)) (fun i => E 3 (ym ν i / 512)) ++
    (lwFamsg E k8 (List.range nLinkFam) (lwK13g k8)).1))))),
   (lwFamsg E k8 (List.range nLinkFam) (lwK13g k8)).2⟩

end LWg

section LW
variable (ν : Rev4.NodeKind) (a b : ℕ)

abbrev lwK9 : ℕ := lwK9g (lwK8 ν a b)
abbrev lwK10 : ℕ := lwK10g (lwK8 ν a b)
abbrev lwK11 : ℕ := lwK11g (lwK8 ν a b)
abbrev lwK12 : ℕ := lwK12g (lwK8 ν a b)
abbrev lwK13 : ℕ := lwK13g (lwK8 ν a b)
abbrev lwEθ (s : ℕ) : LinT := lwEθg (lwK8 ν a b) s
abbrev lwEτ (σ o : ℕ) : LinT := lwEτg (lwK8 ν a b) σ o
abbrev lwEP (σ o : ℕ) : LinT := lwEPg (lwK8 ν a b) σ o
abbrev lwEM (σ o : ℕ) : LinT := lwEMg (lwK8 ν a b) σ o
abbrev lwFams (fs : List ℕ) (k : ℕ) : List Gate × List LinT := lwFamsg (lwE ν a b) (lwK8 ν a b) fs k

/-- **The node kind `ν`'s `linkWAll` template** (inputs `tt : AF a`, then `rr : AF b`): its tables
built once, their entries read from arrays. -/
def tplLW : Tpl :=
  let T := lwT ν a b
  let A := T.2.toArray.map List.toArray
  tplLWg ν (fun j i => (A.getD j #[]).getD i []) (nlocs T.1) T.1

end LW

theorem lwFamsg_len (E : ℕ → ℕ → LinT) (k8 : ℕ) : ∀ (fs : List ℕ) (k : ℕ),
    (lwFamsg E k8 fs k).2.length = fs.length
  | [], _ => rfl
  | f :: fs, k => by simp [lwFamsg, lwFamsg_len E k8 fs]

theorem getD_toArray2 {α : Type} (l : List (List α)) (j i : ℕ) (d : α) :
    ((l.toArray.map List.toArray).getD j #[]).getD i d = (l.getD j []).getD i d := by
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  rcases l[j]? with _ | x <;> simp

/-- **`tplLW` is the template over the spec accessors** (`lwE`, `lwK8`). -/
theorem tplLW_eq (ν : Rev4.NodeKind) (a b : ℕ) :
    tplLW ν a b = tplLWg ν (lwE ν a b) (lwK8 ν a b) (lwT ν a b).1 := by
  have h : (fun j i => (((lwT ν a b).2.toArray.map List.toArray).getD j #[]).getD i []) = lwE ν a b :=
    funext fun j => funext fun i => getD_toArray2 _ j i []
  simp only [tplLW]
  rw [h]
  rfl

theorem tplLW_outs (ν : Rev4.NodeKind) (a b : ℕ) : (tplLW ν a b).outs.length = nLinkFam := by
  rw [tplLW_eq]; simp [tplLWg, lwFamsg_len]

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
    simp only [lwFams, lwFamsg, Eqns.append] at h
    simp only [lwFams, lwFamsg, List.map_cons]
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
  rw [tplLW_eq] at h ⊢
  simp only [tplLWg, Eqns.append, mulsG_nlocs, zero_add] at h
  obtain ⟨hT, h9, h10, h11, h12, h13, hF⟩ := h
  have hE := lwE_ev hi h1 hT
  have h9' : Eqns e (mulsG 256 (lwE ν tt.size rr.size 4) fun _ => lwE ν tt.size rr.size 5 0)
    (lwK8 ν tt.size rr.size) := h9
  have e10 := mulsG_eqns (k := lwK9g (lwK8 ν tt.size rr.size)) h10
  have e11 := mulsG_eqns (k := lwK10g (lwK8 ν tt.size rr.size)) h11
  have e12 := mulsG_eqns (k := lwK11g (lwK8 ν tt.size rr.size)) h12
  have e13 := mulsG_eqns (k := lwK12g (lwK8 ν tt.size rr.size)) h13
  have hF' : Eqns e (lwFams ν tt.size rr.size (List.range nLinkFam) (lwK13 ν tt.size rr.size)).1
    (lwK13 ν tt.size rr.size) := hF
  show (lwFams ν tt.size rr.size (List.range nLinkFam) (lwK13 ν tt.size rr.size)).2.map (LinT.ev e) = _
  rw [linkWAll4I_eq']
  simp only [encV, Array.toList_ofFn]
  rw [ofFn_eq_range _ _ fun f => rfl]
  refine lwFams_ev (ν := ν) (a := tt.size) (b := rr.size) (e := e)
    (EP := lwEPA ν tt rr) (Eτ := lwEτA ν tt) (EM := lwEMA ν rr) (Pr := lwPr ν rr) (Eθ := lwEθA ν tt)
    h1 ?_ (fun i => (hE i).2.2.2.2.2.2.1) (fun i => (hE i).2.2.2.2.2.2.2) ?_ ?_ ?_
    (List.range nLinkFam) (lwK13 ν tt.size rr.size) (fun f hf => List.mem_range.1 hf) hF'
  · intro s
    rw [lwEθ, lwEθg, pL_ev h9', lwEθA, ofFn_getD]
    split_ifs with hs
    · rw [(hE s).2.2.2.2.1, (hE 0).2.2.2.2.2.1, NodeI.eq10, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs]; rfl
    · rfl
  · intro σ hσ o
    unfold lwEτ lwEτg
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := xw_split hσ ho.2
      rw [ev_L, e10 _ d3, (hE _).1, (hE _).2.1, xw, d1, d2, lwEτA, ofFn_getD, dif_pos ho.2, bt_eq_mul]
    · rw [lwEτA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl
  · intro σ hσ o
    unfold lwEP lwEPg
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := xw_split hσ ho.2
      rw [ev_L, e12 _ d3, ev_L, ev_L, e10 _ d3, e11 _ d3, (hE _).1, (hE _).2.1, (hE _).2.2.1, (hE _).2.2.2.1,
        xw, d1, d2, lwEPA, ofFn_getD, dif_pos ho.2, lwEτA, ofFn_getD, dif_pos ho.2, bt_eq_mul, bt_eq_mul]
    · rw [lwEPA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl
  · intro σ hσ o
    unfold lwEM lwEMg
    split_ifs with ho
    · obtain ⟨d1, d2, d3⟩ := ym_split hσ ho.2
      rw [ev_L, e13 _ d3, (hE _).2.2.1, (hE _).2.2.2.1, ym, d1, d2, lwEMA, ofFn_getD, dif_pos ho.2, bt_eq_mul]
    · rw [lwEMA, ofFn_getD, dif_neg fun h' => ho ⟨hσ, h'⟩]; rfl

end Proof

end Tpl
end FR

end G6_FRVIRTplRepLW

section G6_FRVerifierImplNode4T

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `targetS` on a node; stage S-CN4b). 3.x
-- template: `FRVerifierImplNode` (`pfx`, `twoF`, `sepSum`, `tabs`, `rangeI`, `ctrI`, `clsTab`,
-- `gArr`, `targetSNodeI`, `targetSNode_meets`), ported from base 256 to base 512.

/-!
# The revision 4.1 node's `targetS`, computed (`targetSNode4I`), and `implN4` with it

* **Base-512 two-level tables.** `eq(r_blk, x) = A[x mod 512] · B[⌊x/512⌋]` (S-CN4's `bt`: `A` the
  `eq` table of the low 9 block coordinates, `B` of the high `nb − 9`), with prefix arrays over 512
  entries (`pfx9`, additions only). A separable weight `R(⌊x/512⌋) · C(x mod 512)` summed over a
  block range costs four products (`twoF9_eq`, `sepSum9_eq`): every range sum of `eq(r_blk, ·)`
  (`rangeI9`). The stream counters (`ctrK`, `ctrArr`): bit `j < 9` of the counter is a mask on
  the columns, bit `j ≥ 9` a mask on the rows split by the column carry; one pass over the columns
  (`col3`) and the range's rows summed directly (`sepD`), the carry classes shared by every `j`.
* **`targetSNode4I ν r`**: `Gc4`'s ten class weights (`clsW` at `eq9`/`rangeI9`), the counter bits
  of the stream bodies (`ctrArr`, `ctrG`) and of the final blocks (`finG`), `w43`'s step fields,
  then `G` at the 1,153 pinned positions (`gArr4`) and `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`.
  **`targetSNode4_meets`**: it is `targetSNode4S`.
* **`implN4T base ν = implN4 base targetSNode4I ν`** and **`implN4T_meets`**, without the `tS`
  hypothesis.
-/

namespace FR
namespace NI4T
open Finset RecursionFast Rev4 Impl NodeT NT4 NT4C NI4 FR.Stream

/-! ## Base-512 prefix sums -/

/-- The 513 prefix sums of `g` on `0 … 511`. -/
def pfx9 (g : ℕ → F) : Array F := (NodeI.pfxAux g 512).1

theorem pfxAux_getD (g : ℕ → F) (k : ℕ) {i : ℕ} (hi : i ≤ k) :
    (NodeI.pfxAux g k).1.getD i 0 = ∑ l ∈ range i, g l := by
  rw [NodeI.pfxAux_eq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dif_pos (Nat.lt_succ_of_le hi), Option.getD_some]

theorem pfx9_getD (g : ℕ → F) {i : ℕ} (hi : i ≤ 512) :
    (pfx9 g).getD i 0 = ∑ l ∈ range i, g l := pfxAux_getD g 512 hi

/-- `Σ_{x<X} R(⌊x/512⌋) C(x mod 512)` from the prefix arrays `PR`, `PC`. -/
def twoF9 (PR : Array F) (R : ℕ → F) (PC : Array F) (X : ℕ) : F :=
  PR.getD (X / 512) 0 * PC.getD 512 0 + R (X / 512) * PC.getD (X % 512) 0

theorem twoF9_eq (R C : ℕ → F) {X : ℕ} (hX : X ≤ 2 ^ 18) :
    twoF9 (pfx9 R) R (pfx9 C) X = ∑ x ∈ range X, R (x / 512) * C (x % 512) := by
  have hh : X / 512 ≤ 512 := by omega
  have hl : X % 512 ≤ 512 := by omega
  unfold twoF9
  rw [pfx9_getD _ hh, pfx9_getD _ le_rfl, pfx9_getD _ hl]
  conv_rhs => rw [← Nat.div_add_mod X 512, Finset.sum_range_add, mul_comm 512, sum_range_mul]
  rw [Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 512 + k) / 512 = h by omega, show (h * 512 + k) % 512 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 512 * 512 + k) / 512 = X / 512 by omega,
      show (X / 512 * 512 + k) % 512 = k by omega]

/-- **A separable weight over a block range**: `Σ_{k<n} R(⌊(lo+k)/512⌋) C((lo+k) mod 512)`. -/
def sepSum9 (PR : Array F) (R : ℕ → F) (PC : Array F) (lo n : ℕ) : F :=
  twoF9 PR R PC (lo + n) - twoF9 PR R PC lo

theorem sepSum9_eq (R C : ℕ → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 18) :
    sepSum9 (pfx9 R) R (pfx9 C) lo n =
      ∑ k ∈ range n, R ((lo + k) / 512) * C ((lo + k) % 512) := by
  rw [sepSum9, twoF9_eq R C h, twoF9_eq R C (by omega), Finset.sum_range_add, add_sub_cancel_left]

/-! ## The block point's tables -/

/-- The tables of an `n`-coordinate block point (`bt`) and their prefix arrays. -/
def tabs9 (n : ℕ) (a : Array F) : NodeI.Tabs :=
  let T := bt n a
  ⟨T.A, T.B, pfx9 fun l => T.A.getD l 0, pfx9 fun h => T.B.getD h 0⟩

/-- `eq(r_blk, x)` from the tables (one product). -/
def eq9 (T : NodeI.Tabs) (x : ℕ) : F := T.a (x % 512) * T.b (x / 512)

/-- `Σ_{k<n} eq(r_blk, lo + k)` (four products). -/
def rangeI9 (T : NodeI.Tabs) (lo n : ℕ) : F := sepSum9 T.PB T.b T.PA lo n

section TabsLemmas
variable {n : ℕ} (a : Array F)

theorem tabs9_a (l : ℕ) : (tabs9 n a).a l = (bt n a).A.getD l 0 := by simp only [tabs9, NodeI.Tabs.a]
theorem tabs9_b (h : ℕ) : (tabs9 n a).b h = (bt n a).B.getD h 0 := by simp only [tabs9, NodeI.Tabs.b]
theorem tabs9_PA : (tabs9 n a).PA = pfx9 fun l => (tabs9 n a).a l := by
  simp only [tabs9, NodeI.Tabs.a]
theorem tabs9_PB : (tabs9 n a).PB = pfx9 fun h => (tabs9 n a).b h := by
  simp only [tabs9, NodeI.Tabs.b]

variable (hn : 9 ≤ n)
include hn

theorem eq9_eq {x : ℕ} (hx : x < 2 ^ n) : eq9 (tabs9 n a) x = eqAtR (ptA n a) x := by
  rw [eq9, tabs9_a, tabs9_b, ← bt_eq hn a hx, BT.eq]

theorem ba9_eq {x : ℕ} (hx : x < 2 ^ n) :
    (tabs9 n a).b (x / 512) * (tabs9 n a).a (x % 512) = eqAtR (ptA n a) x := by
  rw [← eq9_eq a hn hx, eq9, mul_comm]

theorem rangeI9_eq (hn' : n ≤ 18) {lo m : ℕ} (h : lo + m ≤ 2 ^ n) :
    rangeI9 (tabs9 n a) lo m = ∑ k ∈ range m, eqAtR (ptA n a) (lo + k) := by
  have h18 : 2 ^ n ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn'
  rw [rangeI9, tabs9_PA, tabs9_PB, sepSum9_eq _ _ (by omega)]
  exact Finset.sum_congr rfl fun k hk => ba9_eq a hn (by have := Finset.mem_range.1 hk; omega)

end TabsLemmas

/-! ## The stream counters -/

/-- One pass over the 512 columns, cut at `l₀` and `l₁`:
`(Σ_{l<512} C l, Σ_{l<l₀} C l, Σ_{l<l₁} C l)`. -/
def colT (C : ℕ → F) (l0 l1 : ℕ) : F × F × F :=
  let a := min l0 l1
  let b := max l0 l1
  let s1 := sumTo a C
  let s2 := sumTo (b - a) fun i => C (a + i)
  let s3 := sumTo (512 - b) fun i => C (b + i)
  (s1 + s2 + s3, if l0 ≤ l1 then s1 else s1 + s2, if l0 ≤ l1 then s1 + s2 else s1)

theorem colT_eq (C : ℕ → F) {l0 l1 : ℕ} (h0 : l0 ≤ 512) (h1 : l1 ≤ 512) : colT C l0 l1 =
    (∑ l ∈ range 512, C l, ∑ l ∈ range l0, C l, ∑ l ∈ range l1, C l) := by
  have e1 := Finset.sum_range_add C (min l0 l1) (max l0 l1 - min l0 l1)
  have e2 := Finset.sum_range_add C (max l0 l1) (512 - max l0 l1)
  rw [show min l0 l1 + (max l0 l1 - min l0 l1) = max l0 l1 by omega] at e1
  rw [show max l0 l1 + (512 - max l0 l1) = 512 by omega] at e2
  simp only [colT, sumTo_eq]
  refine Prod.ext (by rw [e2, e1]) (Prod.ext ?_ ?_) <;> dsimp only <;> split_ifs with h
  · rw [show min l0 l1 = l0 by omega]
  · rw [← e1, show max l0 l1 = l0 by omega]
  · rw [← e1, show max l0 l1 = l1 by omega]
  · rw [show min l0 l1 = l1 by omega]

/-- **A separable weight over a block range** from its row weight `R` and the column sums
`t = (Σ_{l<512} C, Σ_{l<lo mod 512} C, Σ_{l<(lo+n) mod 512} C)`: the rows of the range are summed
directly (no prefix array). -/
def sepD (R : ℕ → F) (t : F × F × F) (lo n : ℕ) : F :=
  (sumTo ((lo + n) / 512 - lo / 512) fun i => R (lo / 512 + i)) * t.1 +
    R ((lo + n) / 512) * t.2.2 - R (lo / 512) * t.2.1

theorem twoG_eq (R C : ℕ → F) (X : ℕ) :
    (∑ h ∈ range (X / 512), R h) * (∑ l ∈ range 512, C l) + R (X / 512) * ∑ l ∈ range (X % 512), C l =
      ∑ x ∈ range X, R (x / 512) * C (x % 512) := by
  conv_rhs => rw [← Nat.div_add_mod X 512, Finset.sum_range_add, mul_comm 512, sum_range_mul]
  rw [Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 512 + k) / 512 = h by omega, show (h * 512 + k) % 512 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 512 * 512 + k) / 512 = X / 512 by omega,
      show (X / 512 * 512 + k) % 512 = k by omega]

theorem sepD_eq (R C : ℕ → F) (lo n : ℕ) :
    sepD R (colT C (lo % 512) ((lo + n) % 512)) lo n =
      ∑ k ∈ range n, R ((lo + k) / 512) * C ((lo + k) % 512) := by
  have e := Finset.sum_range_add (fun x => R (x / 512) * C (x % 512)) lo n
  rw [← twoG_eq, ← twoG_eq] at e
  rw [sepD, colT_eq _ (by omega) (by omega), sumTo_eq]
  dsimp only
  have e2 := Finset.sum_range_add R (lo / 512) ((lo + n) / 512 - lo / 512)
  rw [show lo / 512 + ((lo + n) / 512 - lo / 512) = (lo + n) / 512 by
    have : lo / 512 ≤ (lo + n) / 512 := Nat.div_le_div_right (by omega); omega] at e2
  rw [e2] at e
  linear_combination e

/-- The column factor of a body's counter bit `j ≥ 9`: no carry (`b = false`) or a carry out of the
column (`b = true`) for the column offset `d`. -/
def cc (T : NodeI.Tabs) (d : ℕ) (b : Bool) (l : ℕ) : F :=
  if b then (if l + d < 512 then 0 else T.a l) else (if l + d < 512 then T.a l else 0)

/-- The counter's column offset for a body starting at `lo` (`k + 2 = (lo + k) + e − 512 Q`). -/
def eOf (lo : ℕ) : ℕ := 512 * ((lo + 509) / 512) + 2 - lo

/-- **The counter bit `j` of a stream body** `Σ_{k<n} eq(r_blk, lo + k) · bit_j(k + 2)` (3.x's
`ctrI` at base 512): bit `j < 9` is a mask on the columns; bit `j ≥ 9` a mask on the rows, split
by the column carry (`t0`, `t1`: the carry classes' column sums, shared by every `j`); `0` once
`2^j > n + 1`. -/
def ctrK (T : NodeI.Tabs) (lo n : ℕ) (t0 t1 : F × F × F) (j : ℕ) : F :=
  if n + 1 < 2 ^ j then 0 else
  let Q := (lo + 509) / 512
  let e := eOf lo
  if j < 9 then
    sepD T.b (colT (fun l => if ((l + e % 512) % 512).testBit j then T.a l else 0)
      (lo % 512) ((lo + n) % 512)) lo n
  else
    sepD (fun h => if (h + e / 512 - Q).testBit (j - 9) then T.b h else 0) t0 lo n +
      sepD (fun h => if (h + e / 512 + 1 - Q).testBit (j - 9) then T.b h else 0) t1 lo n

/-- **A body's 26 counter bits** (`t_lo`'s bits `6 … 31` of `64 (k + 2)`): a short body
(`n < 512`, a key leaf) directly from its `eq` values; a long one (a chain) by `ctrK`, the carry
classes' column sums computed once. -/
def ctrArr (T : NodeI.Tabs) (lo n : ℕ) : Array F :=
  if n < 512 then
    let E := Array.ofFn (n := n) fun k => eq9 T (lo + k)
    Array.ofFn (n := 26) fun j => sumTo n fun k => if (k + 2).testBit j then E.getD k 0 else 0
  else
    let d := eOf lo % 512
    let t0 := colT (cc T d false) (lo % 512) ((lo + n) % 512)
    let t1 := colT (cc T d true) (lo % 512) ((lo + n) % 512)
    Array.ofFn (n := 26) fun j => ctrK T lo n t0 t1 j

theorem ctrK_eq {nb : ℕ} (hn : 9 ≤ nb) (a : Array F) {lo n : ℕ} (h : lo + n ≤ 2 ^ nb) (j : ℕ) :
    ctrK (tabs9 nb a) lo n (colT (cc (tabs9 nb a) (eOf lo % 512) false) (lo % 512) ((lo + n) % 512))
      (colT (cc (tabs9 nb a) (eOf lo % 512) true) (lo % 512) ((lo + n) % 512)) j =
      ∑ k ∈ range n, eqAtR (ptA nb a) (lo + k) * bF ((k + 2).testBit j) := by
  unfold ctrK eOf
  split_ifs with hj hj9
  · refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have := Finset.mem_range.1 hk
    rw [Nat.testBit_lt_two_pow (by omega)]
    simp [bF]
  · rw [sepD_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hb : (k + 2).testBit j = (((lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512)
        % 512).testBit j := by
      rw [show ((lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512) % 512 =
        (k + 2) % 2 ^ 9 by omega, Nat.testBit_mod_two_pow]
      simp [hj9]
    rw [hb, ← ba9_eq a hn (show lo + k < 2 ^ nb by omega)]
    unfold bF
    split_ifs <;> ring
  · dsimp only
    rw [sepD_eq, sepD_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [← ba9_eq a hn (show lo + k < 2 ^ nb by omega)]
    have hb : (k + 2).testBit j = ((k + 2) / 2 ^ 9).testBit (j - 9) := by
      rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
    unfold cc
    by_cases hc : (lo + k) % 512 + (512 * ((lo + 509) / 512) + 2 - lo) % 512 < 512
    · rw [hb, show (k + 2) / 2 ^ 9 = (lo + k) / 512 + (512 * ((lo + 509) / 512) + 2 - lo) / 512 -
        (lo + 509) / 512 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, add_zero, Bool.false_eq_true]
      unfold bF
      split_ifs <;> ring
    · rw [hb, show (k + 2) / 2 ^ 9 = (lo + k) / 512 + (512 * ((lo + 509) / 512) + 2 - lo) / 512 +
        1 - (lo + 509) / 512 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, zero_add, Bool.false_eq_true]
      unfold bF
      split_ifs <;> ring

theorem ctrArr_eq {nb : ℕ} (hn : 9 ≤ nb) (a : Array F) {lo n : ℕ} (h : lo + n ≤ 2 ^ nb) {j : ℕ}
    (hj : j < 26) : (ctrArr (tabs9 nb a) lo n).getD j 0 =
      ∑ k ∈ range n, eqAtR (ptA nb a) (lo + k) * bF ((k + 2).testBit j) := by
  rw [ctrArr]
  split_ifs with hn5
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hj, Option.getD_some, sumTo_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hk', Option.getD_some,
      eq9_eq a hn (by omega), bF]
    split_ifs <;> simp
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hj, Option.getD_some]
    exact ctrK_eq hn a h j

/-! ## `targetSNode4I` -/

/-- The ten classes' pinned bits at the positions `0 … 1152` (computed once). -/
def clsTab4 : Array (Array Bool) :=
  Array.ofFn (n := 10) fun c => Array.ofFn (n := 1153) fun p =>
    cls4 c (ProductCircuit.pos p) == some true

/-- Class `c`'s bit at `p`. -/
def clsBit4 (c p : ℕ) : Bool := (clsTab4.getD c #[]).getD p false

theorem clsBit4_eq {c p : ℕ} (hc : c < 10) (hp : p < 1153) (x : F) :
    (if clsBit4 c p then x else 0) = x * tgtE (cls4 c) p := by
  have : clsBit4 c p = (cls4 c (ProductCircuit.pos p) == some true) := by
    simp [clsBit4, clsTab4, Array.getD_eq_getD_getElem?, hc, hp]
  rw [this, tgtE, bF]
  split_ifs <;> simp

/-- `G(p)` from the class weights `W`, the bodies' counter bits `CT` (positions `1030 … 1055`),
the final blocks' counter bits `FB` (`1024 … 1055`), `w43`'s `i`, `s` bits. -/
def gAt4 (W CT FB WI WS : Array F) (p : ℕ) : F :=
  (if clsBit4 0 p then W.getD 0 0 else 0) + (if clsBit4 1 p then W.getD 1 0 else 0) +
    (if clsBit4 2 p then W.getD 2 0 else 0) + (if clsBit4 3 p then W.getD 3 0 else 0) +
    (if clsBit4 4 p then W.getD 4 0 else 0) + (if clsBit4 5 p then W.getD 5 0 else 0) +
    (if clsBit4 6 p then W.getD 6 0 else 0) + (if clsBit4 7 p then W.getD 7 0 else 0) +
    (if clsBit4 8 p then W.getD 8 0 else 0) + (if clsBit4 9 p then W.getD 9 0 else 0) +
    (if 1030 ≤ p ∧ p < 1056 then CT.getD (p - 1030) 0 else 0) +
    (if 1024 ≤ p ∧ p < 1056 then FB.getD (p - 1024) 0 else 0) +
    (if 584 ≤ p ∧ p < 592 then WI.getD (p - 584) 0 else 0) +
    (if 592 ≤ p ∧ p < 600 then WS.getD (p - 592) 0 else 0)

/-- **`G` at the 1,153 pinned positions** (the rest is `0`). -/
def gArr4 (ν : NodeKind) (T : NodeI.Tabs) : Array F :=
  let W := Array.ofFn (n := 10) fun c => clsW ν (eq9 T) (rangeI9 T) c
  let KA := ctrArr T (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)
  let KB := ctrArr T (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)
  let KC := ctrArr T (N4c.wotsB ν 0 + 400) 65
  let KD := ctrArr T (N4c.wotsB ν 1 + 400) 65
  let CT := Array.ofFn (n := 26) fun j =>
    KA.getD j 0 + KB.getD j 0 + (KC.getD j 0 + KD.getD j 0)
  let FB := Array.ofFn (n := 32) fun j => finG ν (eq9 T) j
  let E0 := Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)
  let E1 := Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)
  let WI := Array.ofFn (n := 8) fun b => NodeI.w43I E0 (· / 3) b + NodeI.w43I E1 (· / 3) b
  let WS := Array.ofFn (n := 8) fun b => NodeI.w43I E0 (· % 3) b + NodeI.w43I E1 (· % 3) b
  Array.ofFn (n := 1153) fun p => gAt4 W CT FB WI WS p

/-- The block coordinates of `targetS`'s operand as an array (`r[1 … nb]`). -/
def rbArr (ν : NodeKind) (r : Array F) : Array F := Array.ofFn (n := nbN ν) (rbOf4 ν r)

/-- **`targetS` of a revision 4.1 node** (A.8), computed: `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`. -/
def targetSNode4I (ν : NodeKind) (r : Array F) : Array F :=
  let G := gArr4 ν (tabs9 (nbN ν) (rbArr ν r))
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 19 fun hi => H.getD hi 0 * G.getD (σ + 64 * hi) 0

section Meets

theorem ite_getD {n i : ℕ} (c : Prop) [Decidable c] (h : c → i < n) (g : Fin n → F) (v : F)
    (hv : ∀ hi : i < n, g ⟨i, hi⟩ = v) :
    (if c then (Array.ofFn g).getD i 0 else 0) = if c then v else 0 := by
  split_ifs with hc
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (h hc), Option.getD_some, hv]
  · rfl

private theorem sum_two (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

/-- `w43`'s step sums from the `e` arrays are `stepG` at `eq9`. -/
theorem w43_eq (ν : NodeKind) (T : NodeI.Tabs) (sel : ℕ → ℕ) (b : ℕ) :
    NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) sel b +
      NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) sel b =
      stepG ν (eq9 T) sel b := by
  have h : ∀ σ, NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν σ + o)) sel b =
      sumTo 399 fun o => eq9 T (N4c.wotsB ν σ + o) * bF ((sel o).testBit b) := fun σ => by
    simp only [NodeI.w43I, sumTo_eq]
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (Finset.mem_range.1 ho),
      Option.getD_some, bF]
    split_ifs <;> simp
  rw [h, h, stepG]
  simp only [sumTo_eq, sum_two]

/-- **`G`, computed, is the closed form** at every pinned position. -/
theorem gArr4_eq (ν : NodeKind) (a : Array F) {p : ℕ} (hp : p < 1153) :
    (gArr4 ν (tabs9 (nbN ν) a)).getD p 0 = Gc4 ν (eqAtR (ptA (nbN ν) a)) p := by
  obtain ⟨hn9, hn18⟩ := nbN_bounds ν
  have hE := (lay_bounds ν).2.2.2.2
  have hpt : ∀ x < N4c.hEnd ν, eq9 (tabs9 (nbN ν) a) x = eqAtR (ptA (nbN ν) a) x :=
    fun x hx => eq9_eq a hn9 (by omega)
  have hrng : ∀ lo n, lo + n ≤ N4c.hEnd ν →
      rangeI9 (tabs9 (nbN ν) a) lo n = rngS (eqAtR (ptA (nbN ν) a)) lo n :=
    fun lo n h => rangeI9_eq a hn9 hn18 (by omega)
  have hct : ∀ j < 26, (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
      (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
      ((ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 0 + 400) 65).getD j 0 +
        (ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + 400) 65).getD j 0) =
      ctrG ν (ctrS (eqAtR (ptA (nbN ν) a))) j := fun j hj => by
    obtain ⟨b1, -, b3, -, -⟩ := lay_bounds ν
    have c0 := (chain_facts ν (σ := 0) (by norm_num)).2.1
    have c1 := (chain_facts ν (σ := 1) (by norm_num)).2.1
    have := b1 0 (by norm_num); have := b1 1 (by norm_num)
    have := b3 0 (by norm_num); have := b3 1 (by norm_num)
    rw [ctrArr_eq hn9 a (by omega) hj, ctrArr_eq hn9 a (by omega) hj, ctrArr_eq hn9 a (by omega) hj,
      ctrArr_eq hn9 a (by omega) hj, ctrG, sumTo_eq, sumTo_eq, sum_two, sum_two]
    rfl
  have hW : ∀ c (hc : c < 10), (Array.ofFn (n := 10) fun c =>
      clsW ν (eq9 (tabs9 (nbN ν) a)) (rangeI9 (tabs9 (nbN ν) a)) c).getD c 0 =
      clsW ν (eqAtR (ptA (nbN ν) a)) (rngS (eqAtR (ptA (nbN ν) a))) c := fun c hc => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hc, Option.getD_some]
    exact clsW_congr ν hpt hrng c
  simp only [gArr4]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp, Option.getD_some]
  unfold gAt4 Gc4
  rw [clsBit4_eq (c := 0) (by norm_num) hp, clsBit4_eq (c := 1) (by norm_num) hp,
    clsBit4_eq (c := 2) (by norm_num) hp, clsBit4_eq (c := 3) (by norm_num) hp,
    clsBit4_eq (c := 4) (by norm_num) hp, clsBit4_eq (c := 5) (by norm_num) hp,
    clsBit4_eq (c := 6) (by norm_num) hp, clsBit4_eq (c := 7) (by norm_num) hp,
    clsBit4_eq (c := 8) (by norm_num) hp, clsBit4_eq (c := 9) (by norm_num) hp,
    hW 0 (by norm_num), hW 1 (by norm_num), hW 2 (by norm_num), hW 3 (by norm_num),
    hW 4 (by norm_num), hW 5 (by norm_num), hW 6 (by norm_num), hW 7 (by norm_num),
    hW 8 (by norm_num), hW 9 (by norm_num),
    ite_getD (1030 ≤ p ∧ p < 1056) (fun _ => by omega)
      (fun j : Fin 26 => (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
        (ctrArr (tabs9 (nbN ν) a) (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
        ((ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 0 + 400) 65).getD j 0 +
          (ctrArr (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + 400) 65).getD j 0))
      (ctrG ν (ctrS (eqAtR (ptA (nbN ν) a))) (p - 1030)) (fun hi => hct _ hi),
    ite_getD (1024 ≤ p ∧ p < 1056) (fun _ => by omega)
      (fun j : Fin 32 => finG ν (eq9 (tabs9 (nbN ν) a)) j)
      (finG ν (eq9 (tabs9 (nbN ν) a)) (p - 1024)) (fun _ => rfl),
    ite_getD (584 ≤ p ∧ p < 592) (fun _ => by omega)
      (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a)
          (N4c.wotsB ν 0 + o)) (· / 3) b +
        NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + o))
          (· / 3) b)
      (stepG ν (eq9 (tabs9 (nbN ν) a)) (· / 3) (p - 584)) (fun _ => w43_eq ν _ _ _),
    ite_getD (592 ≤ p ∧ p < 600) (fun _ => by omega)
      (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a)
          (N4c.wotsB ν 0 + o)) (· % 3) b +
        NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 (tabs9 (nbN ν) a) (N4c.wotsB ν 1 + o))
          (· % 3) b)
      (stepG ν (eq9 (tabs9 (nbN ν) a)) (· % 3) (p - 592)) (fun _ => w43_eq ν _ _ _),
    finG_congr ν hpt, stepG_congr ν hpt, stepG_congr ν hpt]

/-- **`targetS` meets the revision 4.1 node's specification.** -/
theorem targetSNode4_meets (ν : NodeKind) (r : Array F) : targetSNode4I ν r = targetSNode4S ν r := by
  rw [targetS_node4_eq]
  unfold targetSNode4I
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  have hσ := σ.isLt
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun hi hh => ?_
  have hh' := Finset.mem_range.1 hh
  rw [eqTable_ofFn_getD _ (show hi < 2 ^ 8 by omega)]
  refine congrArg (eqAtR (zLo r) hi * ·) ?_
  by_cases hq : σ.val + 64 * hi < 1153
  · rw [gArr4_eq ν _ hq, rbArr, NodeI.ptA_ofFn]
  · rw [Gc4_hi _ _ (by omega) (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simp only [gArr4, Array.size_ofFn]; omega)]
    rfl

end Meets

/-! ## The node's op implementation with `targetSNode4I` -/

/-- **`implN4T base ν`**: S-CN4's `implN4` with the computed `targetS`. -/
def implN4T (base : NodeKind → OpImpl) (ν : NodeKind) : OpImpl :=
  implN4 base (fun ν => targetSNode4I ν) ν

/-- **`implN4T ⊨ specN4`**, given the base's ops only. -/
theorem implN4T_meets {base : NodeKind → OpImpl} {spec : NodeKind → OpSpec} (ν : NodeKind)
    (h : (base ν).Meets (spec ν)) : (implN4T base ν).Meets (specN4 spec ν) :=
  implN4_meets ν h fun r => targetSNode4_meets ν r

/-! ## Controls -/

section Controls

/-- At a Boolean block point the block sum reads the block's target: `G(p) = E(b, p)`. -/
theorem blkW4_cube (ν : NodeKind) {b : ℕ} (hb : b < 2 ^ nbN ν) (p : ℕ) :
    blkW4 ν (eqAtR (cubeN (nbN ν) b)) p = nodeE4 ν b p := by
  unfold blkW4
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.2 hb) fun x hx hne => by
    rw [eqAtR_cubeN hb (Finset.mem_range.1 hx), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN hb hb, if_pos rfl, one_mul]

/-- (+) **At a Boolean block point `b` the node's `targetS` reads block `b`'s target.** -/
theorem targetSNode4I_blk (ν : NodeKind) (r : Array F) {b : ℕ} (hr : rbOf4 ν r = cubeN (nbN ν) b)
    (hb : b < 2 ^ nbN ν) : targetSNode4I ν r = Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 256, eqAtR (zLo r) hi * nodeE4 ν b (σ + 64 * hi) := by
  rw [targetSNode4_meets, targetSNode4_blk, hr]
  exact congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_congr rfl fun hi _ => by
    rw [blkW4_cube ν hb])

/-- A block of an interval of the layout reads the interval's target. -/
theorem nodeE4_of_mem {ν : NodeKind} {iv : N4c.TIv} (h : iv ∈ N4c.nodeLayout4 ν) {blk : ℕ}
    (hk : iv.mem blk = true) (p : ℕ) : nodeE4 ν blk p = tF (iv.tgt (blk - iv.lo)) p := by
  rw [nodeE4_tF, N4c.tgt_of_mem h hk]

/-- (−) **At a `free` block point past `hEnd` the node's `targetS` is zero.** -/
theorem targetSNode4I_free (ν : NodeKind) (r : Array F) {b : ℕ} (hr : rbOf4 ν r = cubeN (nbN ν) b)
    (h1 : N4c.hEnd ν ≤ b) (hb : b < 2 ^ nbN ν) :
    targetSNode4I ν r = Array.ofFn (n := 64) fun _ => 0 := by
  have hm : N4c.freeIv (N4c.hEnd ν) ν.blocks ∈ N4c.nodeLayout4 ν := by
    simp only [N4c.nodeLayout4, List.mem_append, List.mem_singleton, or_true]
  have hk : (N4c.freeIv (N4c.hEnd ν) ν.blocks).mem b = true := by
    simp only [N4c.TIv.mem, N4c.freeIv, Bool.and_eq_true]
    exact ⟨decide_eq_true h1, decide_eq_true hb⟩
  rw [targetSNode4I_blk ν r hr hb]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_eq_zero fun hi _ => ?_)
  rw [nodeE4_of_mem hm hk]
  show eqAtR (zLo r) hi * tF none _ = 0
  rw [tF, mul_zero]

/-- The target bit of a stream block as a Boolean (`tgtE = bF ∘ ·`). -/
theorem tgtE_bit (t : Block.Target) (p : ℕ) :
    tgtE t p = bF (t (ProductCircuit.pos p) == some true) := rfl

/-- (+/−) **The bits on `N4`**: chain 0's block 1 (counter `128`) reads `t_lo` bit 7 as `1` and
bit 6 as `0`; chain 1's last block (final, `t = aggB 4 = 64 · 96,950`, R-A′'s whole blocks) reads
bit 7 and the final flag as `1` and bit 0 as `0`, its second-to-last block reads the flag as `0`; the tail's candidate `F_{0,1}` (final,
`t = aggB 1 = 0x17AB00`, revision 4.4.2, RSV2) reads the flag and bit 13 as `1`, bit 12 as `0`. -/
theorem nodeE4_ctrl :
    nodeE4 .N4 1 1031 = 1 ∧ nodeE4 .N4 1 1030 = 0 ∧
    nodeE4 .N4 (lastB .N4 1) 1031 = 1 ∧ nodeE4 .N4 (lastB .N4 1) 1024 = 0 ∧
    nodeE4 .N4 (lastB .N4 1) 1088 = 1 ∧
    nodeE4 .N4 (lastB .N4 1 - 1) 1088 = 0 ∧
    nodeE4 .N4 (N4c.finB .N4 0) 1088 = 1 ∧ nodeE4 .N4 (N4c.finB .N4 0) 1037 = 1 ∧
    nodeE4 .N4 (N4c.finB .N4 0) 1036 = 0 := by
  have hc0 : (⟨.stream, N4c.chBase .N4 0 + 1, N4c.chBase .N4 0 + N4c.chLen .N4 0,
      fun o => some (streamTarget (N4c.chBytes .N4 0) (o + 1))⟩ : N4c.TIv) ∈ N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.chainIvs, List.mem_append, List.mem_cons, true_or, or_true]
  have hc1 : (⟨.stream, N4c.chBase .N4 1 + 1, N4c.chBase .N4 1 + N4c.chLen .N4 1,
      fun o => some (streamTarget (N4c.chBytes .N4 1) (o + 1))⟩ : N4c.TIv) ∈ N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.chainIvs, List.mem_append, List.mem_cons, true_or, or_true]
  have ht : (⟨.stream, N4c.finB .N4 0 + 0, N4c.finB .N4 0 + 0 + 1,
      fun _ => some (streamTarget (N4c.aggB (0 + 1)) (N4c.aggL (0 + 1) - 1))⟩ : N4c.TIv) ∈
      N4c.nodeLayout4 .N4 := by
    simp only [N4c.nodeLayout4, N4c.tailIvs, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_range, List.mem_singleton]
    exact Or.inl (Or.inr ⟨0, by decide, Or.inl ⟨0, by decide, rfl⟩⟩)
  have m0 : ∀ p, nodeE4 .N4 1 p = tgtE (streamTarget (N4c.chBytes .N4 0) 1) p := fun p => by
    rw [nodeE4_of_mem hc0 (by decide)]; rfl
  have m1 : ∀ x, x < N4c.chLen .N4 1 - 1 → ∀ p, nodeE4 .N4 (N4c.chBase .N4 1 + 1 + x) p =
      tgtE (streamTarget (N4c.chBytes .N4 1) (x + 1)) p := fun x hx p => by
    have := (chain_facts .N4 (σ := 1) (by norm_num)).2.1
    rw [nodeE4_of_mem hc1 (by simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega),
      show N4c.chBase .N4 1 + 1 + x - (N4c.chBase .N4 1 + 1) = x by omega]
    rfl
  have mt : ∀ p, nodeE4 .N4 (N4c.finB .N4 0) p = tgtE (blockTarget (N4c.aggB 1) true) p := fun p => by
    rw [nodeE4_of_mem ht (by simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    simp only [tF, fin_target]
  have hl : lastB .N4 1 = N4c.chBase .N4 1 + 1 + (N4c.chLen .N4 1 - 2) := rfl
  have hl' : lastB .N4 1 - 1 = N4c.chBase .N4 1 + 1 + (N4c.chLen .N4 1 - 3) := by
    have := (chain_facts .N4 (σ := 1) (by norm_num)).2.1
    have : 3 ≤ N4c.chLen .N4 1 := by decide
    rw [hl]; omega
  have hL : 3 ≤ N4c.chLen .N4 1 := by decide
  rw [m0, m0, hl', hl, m1 _ (by omega), m1 _ (by omega), m1 _ (by omega), m1 _ (by omega), mt, mt, mt]
  simp only [tgtE_bit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [bF] <;> decide

end Controls

end NI4T
end FR

end G6_FRVerifierImplNode4T

section G6_FRVIRTplRepT

-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).

/-!
# The replay template of a node's `targetS` (`NI4T.targetSNode4I ν`), gate for gate

One node kind's sub-template for the previous node's `targetS` (input `r : AF a`), mirroring
`targetSNode4I ν r` value for value (`T = tabs9 nb (rbArr ν r)`):

* three `eq` tables (`tabsG`): the block point's low 9 and high `nb − 9` coordinates (`r[1 … nb]`,
  S-CN4's `bt`), and `zLo r` (7 pinned constants and `r[0]`: `H`);
* the point weights `eq9 T x` (one product each) at the blocks `clsW`, `finG` and `w43I` read: the
  chain starts and last blocks, the statement blocks, `cAB`, the tails' candidates, the two WOTS
  slots' 498 blocks;
* the range sums `rangeI9 T lo n` (four products each over prefix forms: `twoF9`);
* the counter bits `ctrArr T lo n` of the four stream bodies (a short body: its weights, then
  masks; a chain: `ctrK`'s `sepD`/`colT` at six locals per bit);
* `G` at the 1,153 pinned positions as linear forms (`gAt4`), and the 1,216 products
  `H[hi] · G(σ + 64 hi)`.

**`tplTS_ok`**: with `e.one = 1`, the input `r` and the gate equations, the outputs are
`targetSNode4I ν r`. No operand-register literal is involved: the template is a function of `ν`
and the operand's length.
-/

namespace FR
namespace Tpl
open Circ Finset RecursionFast Rev4 Impl NodeT NT4 NT4C NI4 NI4T FR.Stream

variable {e : Env}

theorem ev_ite (c : Prop) [Decidable c] (x y : LinT) :
    (if c then x else y).ev e = if c then x.ev e else y.ev e := by
  split_ifs <;> rfl

theorem pfx9_getD' (g : ℕ → F) (i : ℕ) : (pfx9 g).getD i 0 = if i ≤ 512 then ∑ l ∈ range i, g l else 0 := by
  split_ifs with h
  · exact pfx9_getD g h
  · simp only [pfx9, NodeI.pfxAux_eq, ofFn_getD]
    rw [dif_neg (by omega)]

/-! ## Pieces over the two-level tables (entries `TA`, `TB`) -/

section Pieces
variable (TA TB : ℕ → LinT)

/-- The prefix forms (`pfx9`'s entries; `0` past `512`). -/
def tsPA (i : ℕ) : LinT := if i ≤ 512 then sumG i TA else []
def tsPB (i : ℕ) : LinT := if i ≤ 512 then sumG i TB else []

/-- Gate `i` of a range-sum block reads the end (`i mod 4 < 2`) or the start of range `⌊i/4⌋`. -/
def tsRX (f : ℕ → ℕ × ℕ) (i : ℕ) : ℕ := if i % 4 < 2 then (f (i / 4)).1 + (f (i / 4)).2 else (f (i / 4)).1

/-- **Range sums** `Σ_{k<n_q} eq(·, lo_q + k)` for `q < n` (`f q = (lo_q, n_q)`): `twoF9` at the end
and at the start, two products each. -/
def tsRngG (f : ℕ → ℕ × ℕ) (n : ℕ) : List Gate :=
  mulsG (4 * n) (fun i => if i % 2 = 0 then tsPB TB (tsRX f i / 512) else TB (tsRX f i / 512))
    (fun i => if i % 2 = 0 then tsPA TA 512 else tsPA TA (tsRX f i % 512))

/-- Range `q`'s sum. -/
def tsRngF (k q : ℕ) : LinT :=
  L (k + 4 * q) ++ L (k + (4 * q + 1)) ++ sc (-1) (L (k + (4 * q + 2))) ++ sc (-1) (L (k + (4 * q + 3)))

/-- `colT` over forms. -/
def tsColT (C : ℕ → LinT) (l0 l1 : ℕ) : LinT × LinT × LinT :=
  let a := min l0 l1
  let b := max l0 l1
  let s1 := sumG a C
  let s2 := sumG (b - a) fun i => C (a + i)
  let s3 := sumG (512 - b) fun i => C (b + i)
  (s1 ++ s2 ++ s3, if l0 ≤ l1 then s1 else s1 ++ s2, if l0 ≤ l1 then s1 ++ s2 else s1)

/-- `cc` over forms. -/
def tsCc (d : ℕ) (b : Bool) (l : ℕ) : LinT :=
  if b then (if l + d < 512 then [] else TA l) else (if l + d < 512 then TA l else [])

/-- `sepD`'s three products. -/
def tsSepG (R : ℕ → LinT) (t : LinT × LinT × LinT) (lo n : ℕ) : List Gate :=
  [.mul (sumG ((lo + n) / 512 - lo / 512) fun i => R (lo / 512 + i)) t.1, .mul (R ((lo + n) / 512)) t.2.2,
   .mul (R (lo / 512)) t.2.1]

def tsSepF (k : ℕ) : LinT := L k ++ L (k + 1) ++ sc (-1) (L (k + 2))

/-- **A chain's counter bit `j`** (`ctrK`), six locals. -/
def tsCtrKG (lo n j : ℕ) : List Gate :=
  if n + 1 < 2 ^ j then [.pad 0 6]
  else if j < 9 then
    tsSepG TB (tsColT (fun l => if ((l + eOf lo % 512) % 512).testBit j then TA l else [])
      (lo % 512) ((lo + n) % 512)) lo n ++ [.pad 0 3]
  else
    tsSepG (fun h => if (h + eOf lo / 512 - (lo + 509) / 512).testBit (j - 9) then TB h else [])
        (tsColT (tsCc TA (eOf lo % 512) false) (lo % 512) ((lo + n) % 512)) lo n ++
      tsSepG (fun h => if (h + eOf lo / 512 + 1 - (lo + 509) / 512).testBit (j - 9) then TB h else [])
        (tsColT (tsCc TA (eOf lo % 512) true) (lo % 512) ((lo + n) % 512)) lo n

def tsCtrKO (n j k : ℕ) : LinT :=
  if n + 1 < 2 ^ j then [] else if j < 9 then tsSepF k else tsSepF k ++ tsSepF (k + 3)

/-- Bits `0 … m−1`. -/
def tsCtrKs (lo n : ℕ) : ℕ → List Gate
  | 0 => []
  | j + 1 => tsCtrKs lo n j ++ tsCtrKG TA TB lo n j

/-- **A body's 26 counter bits** (`ctrArr`): a short body's weights; a chain's 26 × 6 locals. -/
def tsCtrG (lo n : ℕ) : List Gate :=
  if n < 512 then mulsG n (fun i => TA ((lo + i) % 512)) (fun i => TB ((lo + i) / 512))
  else tsCtrKs TA TB lo n 26

def tsCtrO (lo n k j : ℕ) : LinT :=
  if j < 26 then
    (if n < 512 then sumG n (fun i => if (i + 2).testBit j then L (k + i) else []) else tsCtrKO n j (k + 6 * j))
  else []

end Pieces

def tsCtrN (n : ℕ) : ℕ := if n < 512 then n else 156

theorem tsRngG_nlocs (TA TB : ℕ → LinT) (f : ℕ → ℕ × ℕ) (n : ℕ) : nlocs (tsRngG TA TB f n) = 4 * n :=
  mulsG_nlocs _ _ _

theorem tsCtrKG_nlocs (TA TB : ℕ → LinT) (lo n j : ℕ) : nlocs (tsCtrKG TA TB lo n j) = 6 := by
  unfold tsCtrKG; split_ifs <;> rfl

theorem tsCtrKs_nlocs (TA TB : ℕ → LinT) (lo n : ℕ) : ∀ m, nlocs (tsCtrKs TA TB lo n m) = 6 * m
  | 0 => rfl
  | m + 1 => by rw [tsCtrKs, nlocs_append, tsCtrKs_nlocs TA TB lo n m, tsCtrKG_nlocs]; ring

theorem tsCtrG_nlocs (TA TB : ℕ → LinT) (lo n : ℕ) : nlocs (tsCtrG TA TB lo n) = tsCtrN n := by
  unfold tsCtrG tsCtrN; split_ifs
  · exact mulsG_nlocs _ _ _
  · exact tsCtrKs_nlocs _ _ _ _ 26

/-! ## The pieces compute -/

section PiecesEv
variable {TA TB : ℕ → LinT} {T : NodeI.Tabs}

theorem tsPA_ev (hA : ∀ i, (TA i).ev e = T.a i) (hPA : T.PA = pfx9 fun l => T.a l) (i : ℕ) : (tsPA TA i).ev e = T.PA.getD i 0 := by
  rw [hPA, pfx9_getD', tsPA]
  split_ifs
  · rw [sumG_ev]; exact Finset.sum_congr rfl fun l _ => hA l
  · rfl

theorem tsPB_ev (hB : ∀ i, (TB i).ev e = T.b i) (hPB : T.PB = pfx9 fun l => T.b l) (i : ℕ) : (tsPB TB i).ev e = T.PB.getD i 0 := by
  rw [hPB, pfx9_getD', tsPB]
  split_ifs
  · rw [sumG_ev]; exact Finset.sum_congr rfl fun l _ => hB l
  · rfl

theorem tsRngF_ev (hA : ∀ i, (TA i).ev e = T.a i) (hB : ∀ i, (TB i).ev e = T.b i) (hPA : T.PA = pfx9 fun l => T.a l) (hPB : T.PB = pfx9 fun l => T.b l)
    {f : ℕ → ℕ × ℕ} {n k : ℕ} (h : Eqns e (tsRngG TA TB f n) k) {q : ℕ} (hq : q < n) :
    (tsRngF k q).ev e = rangeI9 T (f q).1 (f q).2 := by
  have hm := mulsG_eqns h
  have g0 := hm (4 * q) (by omega)
  have g1 := hm (4 * q + 1) (by omega)
  have g2 := hm (4 * q + 2) (by omega)
  have g3 := hm (4 * q + 3) (by omega)
  simp only [tsRX, show 4 * q % 4 = 0 by omega, show (4 * q + 1) % 4 = 1 by omega,
    show (4 * q + 2) % 4 = 2 by omega, show (4 * q + 3) % 4 = 3 by omega, show 4 * q / 4 = q by omega,
    show (4 * q + 1) / 4 = q by omega, show (4 * q + 2) / 4 = q by omega, show (4 * q + 3) / 4 = q by omega,
    show 4 * q % 2 = 0 by omega, show (4 * q + 1) % 2 = 1 by omega, show (4 * q + 2) % 2 = 0 by omega,
    show (4 * q + 3) % 2 = 1 by omega] at g0 g1 g2 g3
  simp only [Nat.zero_lt_two, Nat.one_lt_two, ite_true, show ¬ (2 < 2) by omega, show ¬ (3 < 2) by omega,
    ite_false, one_ne_zero] at g0 g1 g2 g3
  simp only [tsRngF, ev_append, ev_sc, ev_L, g0, g1, g2, g3, tsPA_ev hA hPA, tsPB_ev hB hPB, hB,
    rangeI9, sepSum9, twoF9, NodeI.Tabs.b]
  ring

theorem tsColT_ev (C : ℕ → LinT) (C' : ℕ → F) (hC : ∀ l, (C l).ev e = C' l) (l0 l1 : ℕ) :
    (tsColT C l0 l1).1.ev e = (colT C' l0 l1).1 ∧ (tsColT C l0 l1).2.1.ev e = (colT C' l0 l1).2.1 ∧
      (tsColT C l0 l1).2.2.ev e = (colT C' l0 l1).2.2 := by
  simp only [tsColT, colT, sumTo_eq]
  refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> simp only [ev_append, sumG_ev, hC]

theorem tsCc_ev (hA : ∀ i, (TA i).ev e = T.a i) (d : ℕ) (b : Bool) (l : ℕ) : (tsCc TA d b l).ev e = cc T d b l := by
  unfold tsCc cc; cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split_ifs <;>
    simp only [ev_nil, hA, NodeI.Tabs.a]

theorem tsSepF_ev {R : ℕ → LinT} {R' : ℕ → F} (hR : ∀ h, (R h).ev e = R' h) {t : LinT × LinT × LinT}
    {t' : F × F × F} (ht : t.1.ev e = t'.1 ∧ t.2.1.ev e = t'.2.1 ∧ t.2.2.ev e = t'.2.2) {lo n k : ℕ}
    (h : Eqns e (tsSepG R t lo n) k) : (tsSepF k).ev e = sepD R' t' lo n := by
  simp only [tsSepG, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨g0, g1, g2⟩ := h
  simp only [tsSepF, ev_append, ev_sc, ev_L, g0, g1, g2, sepD, sumG_ev, sumTo_eq, hR, ht.1, ht.2.1, ht.2.2,
    Nat.add_assoc]
  ring

theorem tsCtrKO_ev (hA : ∀ i, (TA i).ev e = T.a i) (hB : ∀ i, (TB i).ev e = T.b i) {lo n j k : ℕ} (h : Eqns e (tsCtrKG TA TB lo n j) k) :
    (tsCtrKO n j k).ev e = ctrK T lo n (colT (cc T (eOf lo % 512) false) (lo % 512) ((lo + n) % 512))
      (colT (cc T (eOf lo % 512) true) (lo % 512) ((lo + n) % 512)) j := by
  unfold tsCtrKG at h
  unfold tsCtrKO ctrK
  split_ifs at h ⊢ with h1 h2
  · rfl
  · rw [Eqns.append] at h
    refine tsSepF_ev (R' := T.b) hB (tsColT_ev _ _ (fun l => ?_) _ _) h.1
    rw [ev_ite, hA]; simp only [NodeI.Tabs.a]; split_ifs <;> rfl
  · rw [Eqns.append] at h
    have hl : nlocs (tsSepG (fun h => if (h + eOf lo / 512 - (lo + 509) / 512).testBit (j - 9) then TB h else [])
        (tsColT (tsCc TA (eOf lo % 512) false) (lo % 512) ((lo + n) % 512)) lo n) = 3 := rfl
    rw [hl] at h
    simp only [ev_append]
    refine congrArg₂ (· + ·) (tsSepF_ev (fun x => ?_) (tsColT_ev _ _ (tsCc_ev hA _ _) _ _) h.1)
      (tsSepF_ev (fun x => ?_) (tsColT_ev _ _ (tsCc_ev hA _ _) _ _) h.2) <;>
      (rw [ev_ite, hB]; rfl)

theorem tsCtrKs_eqns {lo n : ℕ} : ∀ {m k : ℕ}, Eqns e (tsCtrKs TA TB lo n m) k →
    ∀ j < m, Eqns e (tsCtrKG TA TB lo n j) (k + 6 * j)
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, k, h, j, hj => by
    rw [tsCtrKs, Eqns.append, tsCtrKs_nlocs] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact tsCtrKs_eqns h.1 j hj
    · exact h.2

/-- **A body's counter bits** are `ctrArr`'s. -/
theorem tsCtrO_ev (hA : ∀ i, (TA i).ev e = T.a i) (hB : ∀ i, (TB i).ev e = T.b i) {lo n k : ℕ} (h : Eqns e (tsCtrG TA TB lo n) k) {j : ℕ} (hj : j < 26) :
    (tsCtrO lo n k j).ev e = (ctrArr T lo n).getD j 0 := by
  unfold tsCtrG at h
  unfold tsCtrO ctrArr
  rw [if_pos hj]
  split_ifs at h ⊢ with hn
  · rw [ofFn_getD, dif_pos hj, sumG_ev, sumTo_eq]
    have hm := mulsG_eqns h
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [ev_ite, ev_L, ev_nil, hm i hi, hA, hB, ofFn_getD, dif_pos hi]
    rfl
  · simp only
    rw [ofFn_getD, dif_pos hj]
    exact tsCtrKO_ev hA hB (tsCtrKs_eqns h j hj)

end PiecesEv

/-! ## The node kind's template -/

section TS
variable (ν : NodeKind) (a : ℕ)

/-- The three tables' coordinate forms (`r` on inputs `0 … a−1`). -/
def tsCs : List (List LinT) :=
  [(List.range 9).map (fun l => cT a (1 + l)), (List.range (nbN ν - 9)).map (fun l => cT a (1 + (9 + l))),
   (List.range 8).map fun l => if h : l < 7 then C (pinnedRho ⟨l, h⟩) else cT a 0]

def tsT : List Gate × List (List LinT) := tabsG (tsCs ν a) 0

/-- Entry `i` of table `j`. -/
def tsE (j i : ℕ) : LinT := ((tsT ν a).2.getD j []).getD i []

/-- **The template's context**, built once per instance: the tables' entries (arrays) and the
tables' locals. Every piece below reads it (a piece that recomputed the tables at every reference
made the template quadratic to build). -/
structure TSCx where
  E : ℕ → ℕ → LinT
  k0 : ℕ

def mkCx (ν : NodeKind) (a : ℕ) : TSCx :=
  let T := tsT ν a
  let A := T.2.toArray.map List.toArray
  ⟨fun j i => (A.getD j #[]).getD i [], nlocs T.1⟩

theorem mkCx_k0 (ν : NodeKind) (a : ℕ) : (mkCx ν a).k0 = nlocs (tsT ν a).1 := by simp only [mkCx]

theorem mkCx_E (ν : NodeKind) (a j i : ℕ) : (mkCx ν a).E j i = tsE ν a j i := by
  simp only [mkCx, tsE, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  cases ((tsT ν a).2)[j]? <;> simp

end TS

section TSC
variable (ν : NodeKind) (cx : TSCx)

/-- `cAB`'s, the tails' candidates' count per tail. -/
def tsM : ℕ := ν.maxK - 1

/-- The four stream bodies: both chains, both key leaves. -/
def tsBLo (i : ℕ) : ℕ := if i < 2 then N4c.chBase ν i + 1 else N4c.wotsB ν (i - 2) + 400
def tsBN (i : ℕ) : ℕ := if i < 2 then N4c.chLen ν i - 2 else 65

/-- The stages' first locals. -/
def tsKLa : ℕ := cx.k0 + 2
def tsKSt : ℕ := tsKLa cx + 2
def tsKCA : ℕ := tsKSt cx + 3 * ν.vslots
def tsKFi : ℕ := tsKCA ν cx + N4c.nAgg ν
def tsKW : ℕ := tsKFi ν cx + N4c.nAgg ν * tsM ν
def tsKRA : ℕ := tsKW ν cx + 996
def tsKRB : ℕ := tsKRA ν cx + 4 * 2
def tsKRD : ℕ := tsKRB ν cx + 4 * 2
def tsKRC : ℕ := tsKRD ν cx + 4 * 2
def tsKC0 : ℕ := tsKRC ν cx + 4 * N4c.nAgg ν
def tsKC1 : ℕ := tsKC0 ν cx + tsCtrN (tsBN ν 0)
def tsKC2 : ℕ := tsKC1 ν cx + tsCtrN (tsBN ν 1)
def tsKC3 : ℕ := tsKC2 ν cx + tsCtrN (tsBN ν 2)
def tsKG : ℕ := tsKC3 ν cx + tsCtrN (tsBN ν 3)

/-- The point weights' accessors. -/
def tsCh (σ : ℕ) : LinT := pL (cx.k0) 2 σ
def tsLa (σ : ℕ) : LinT := pL (tsKLa cx) 2 σ
def tsSt (i : ℕ) : LinT := pL (tsKSt cx) (3 * ν.vslots) i
def tsCA (i : ℕ) : LinT := pL (tsKCA ν cx) (N4c.nAgg ν) i
def tsFi (i t : ℕ) : LinT := if i < N4c.nAgg ν ∧ t < tsM ν then L (tsKFi ν cx + (i * tsM ν + t)) else []
def tsW (σ o : ℕ) : LinT := if σ < 2 ∧ o < 498 then L (tsKW ν cx + (498 * σ + o)) else []

/-- The range sums' blocks: the chain bodies, the key leaves' bodies, the WOTS slots, the tails. -/
def tsFA (σ : ℕ) : ℕ × ℕ := (N4c.chBase ν σ + 1, N4c.chLen ν σ - 2)
def tsFB (σ : ℕ) : ℕ × ℕ := (N4c.wotsB ν σ + 400, 65)
def tsFD (σ : ℕ) : ℕ × ℕ := (N4c.wotsB ν σ, 399)
def tsFC (i : ℕ) : ℕ × ℕ := (N4c.finB ν i, ν.maxK - 1)

/-- **The ten class weights** (`clsW`) over the forms. -/
def tsClsW : ℕ → LinT
  | 0 => sumG 2 (tsCh cx)
  | 1 => sumG 2 (tsRngF (tsKRA ν cx)) ++ sumG 2 (tsRngF (tsKRB ν cx))
  | 2 => sumG 2 (tsLa cx) ++ sumG (N4c.nAgg ν) (tsRngF (tsKRC ν cx))
  | 3 => sumG ν.vslots (fun v => tsSt ν cx (3 * v)) ++ sumG (N4c.nAgg ν) (tsCA ν cx)
  | 4 => sumG ν.vslots fun v => tsSt ν cx (3 * v + 1)
  | 5 => sumG ν.vslots (fun v => tsSt ν cx (3 * v + 2)) ++ sumG 2 fun σ => sumG 16 fun t => tsW ν cx σ (467 + 2 * t)
  | 6 => sumG 2 (tsRngF (tsKRD ν cx))
  | 7 => sumG 2 fun σ => tsW ν cx σ 399
  | 8 => sumG 2 fun σ => tsW ν cx σ 465
  | _ => sumG 2 fun σ => sumG 16 fun t => tsW ν cx σ (466 + 2 * t)

/-- The final blocks' counter bit `j` (`finG`). -/
def tsFinG (j : ℕ) : LinT :=
  (sumG 2 fun σ => sc (bF ((N4c.chBytes ν σ).testBit j)) (tsLa cx σ)) ++
    sumG (N4c.nAgg ν) fun i => sumG (tsM ν) fun t => sc (bF ((N4c.aggB (t + 1)).testBit j)) (tsFi ν cx i t)

/-- `w43`'s step field bit `b` over both WOTS slots. -/
def tsW43 (sel : ℕ → ℕ) (b : ℕ) : LinT :=
  sumG 2 fun σ => sumG 399 fun o => if (sel o).testBit b then tsW ν cx σ o else []

/-- The bodies' counter bit `j`. -/
def tsCT (j : ℕ) : LinT :=
  tsCtrO (tsBLo ν 0) (tsBN ν 0) (tsKC0 ν cx) j ++ tsCtrO (tsBLo ν 1) (tsBN ν 1) (tsKC1 ν cx) j ++
    (tsCtrO (tsBLo ν 2) (tsBN ν 2) (tsKC2 ν cx) j ++ tsCtrO (tsBLo ν 3) (tsBN ν 3) (tsKC3 ν cx) j)

/-- **`G(p)`** (`gAt4`). -/
def tsGAt (p : ℕ) : LinT :=
  (if clsBit4 0 p then tsClsW ν cx 0 else []) ++ (if clsBit4 1 p then tsClsW ν cx 1 else []) ++
    (if clsBit4 2 p then tsClsW ν cx 2 else []) ++ (if clsBit4 3 p then tsClsW ν cx 3 else []) ++
    (if clsBit4 4 p then tsClsW ν cx 4 else []) ++ (if clsBit4 5 p then tsClsW ν cx 5 else []) ++
    (if clsBit4 6 p then tsClsW ν cx 6 else []) ++ (if clsBit4 7 p then tsClsW ν cx 7 else []) ++
    (if clsBit4 8 p then tsClsW ν cx 8 else []) ++ (if clsBit4 9 p then tsClsW ν cx 9 else []) ++
    (if 1030 ≤ p ∧ p < 1056 then tsCT ν cx (p - 1030) else []) ++
    (if 1024 ≤ p ∧ p < 1056 then tsFinG ν cx (p - 1024) else []) ++
    (if 584 ≤ p ∧ p < 592 then tsW43 ν cx (· / 3) (p - 584) else []) ++
    (if 592 ≤ p ∧ p < 600 then tsW43 ν cx (· % 3) (p - 592) else [])

def tsG (p : ℕ) : LinT := if p < 1153 then tsGAt ν cx p else []

/-- **The node kind `ν`'s `targetS` template** (input `r : AF a`). -/
def tplTSx (a : ℕ) : Tpl :=
  ⟨(tsT ν a).1 ++
    (mulsG 2 (fun σ => cx.E 0 (N4c.chBase ν σ % 512)) (fun σ => cx.E 1 (N4c.chBase ν σ / 512)) ++
    (mulsG 2 (fun σ => cx.E 0 (lastB ν σ % 512)) (fun σ => cx.E 1 (lastB ν σ / 512)) ++
    (mulsG (3 * ν.vslots) (fun i => cx.E 0 ((N4c.stmtB ν + i) % 512))
      (fun i => cx.E 1 ((N4c.stmtB ν + i) / 512)) ++
    (mulsG (N4c.nAgg ν) (fun i => cx.E 0 (N4c.cAB ν i % 512)) (fun i => cx.E 1 (N4c.cAB ν i / 512)) ++
    (mulsG (N4c.nAgg ν * tsM ν) (fun i => cx.E 0 ((N4c.finB ν (i / tsM ν) + i % tsM ν) % 512))
      (fun i => cx.E 1 ((N4c.finB ν (i / tsM ν) + i % tsM ν) / 512)) ++
    (mulsG 996 (fun i => cx.E 0 ((N4c.wotsB ν (i / 498) + i % 498) % 512))
      (fun i => cx.E 1 ((N4c.wotsB ν (i / 498) + i % 498) / 512)) ++
    (tsRngG (cx.E 0) (cx.E 1) (tsFA ν) 2 ++
    (tsRngG (cx.E 0) (cx.E 1) (tsFB ν) 2 ++
    (tsRngG (cx.E 0) (cx.E 1) (tsFD ν) 2 ++
    (tsRngG (cx.E 0) (cx.E 1) (tsFC ν) (N4c.nAgg ν) ++
    (tsCtrG (cx.E 0) (cx.E 1) (tsBLo ν 0) (tsBN ν 0) ++
    (tsCtrG (cx.E 0) (cx.E 1) (tsBLo ν 1) (tsBN ν 1) ++
    (tsCtrG (cx.E 0) (cx.E 1) (tsBLo ν 2) (tsBN ν 2) ++
    (tsCtrG (cx.E 0) (cx.E 1) (tsBLo ν 3) (tsBN ν 3) ++
    mulsG 1216 (fun i => cx.E 2 (i % 19)) (fun i => tsG ν cx (i / 19 + 64 * (i % 19))))))))))))))))),
   (List.range 64).map fun σ => sumG 19 fun hi => L (tsKG ν cx + (σ * 19 + hi))⟩

end TSC

/-- **The node kind `ν`'s `targetS` template** (input `r : AF a`), its context built once. -/
def tplTS (ν : NodeKind) (a : ℕ) : Tpl := let cx := mkCx ν a; tplTSx ν cx a



/-! ## Correctness -/

theorem ctrArr_getD_big (T : NodeI.Tabs) (lo n : ℕ) {j : ℕ} (hj : 26 ≤ j) : (ctrArr T lo n).getD j 0 = 0 := by
  unfold ctrArr; split_ifs <;> simp only [ofFn_getD] <;> rw [dif_neg (by omega)]

theorem sum_two' (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by simp [Finset.sum_range_succ]

theorem ite_ev_nil (c : Prop) [Decidable c] (x : LinT) : (if c then x else []).ev e = if c then x.ev e else 0 := by
  split_ifs <;> rfl

section Proof
variable {ν : NodeKind} {r : Array F} (hi : InpIs e (r.toList ++ (#[] : Array F).toList))
include hi

/-- **The three tables.** -/
theorem tsE_ev (h1 : e.one = 1) (h : Eqns e (tsT ν r.size).1 0) (i : ℕ) :
    (tsE ν r.size 0 i).ev e = (tabs9 (nbN ν) (rbArr ν r)).a i ∧
    (tsE ν r.size 1 i).ev e = (tabs9 (nbN ν) (rbArr ν r)).b i ∧
    (tsE ν r.size 2 i).ev e = (eqTable (List.ofFn (zLo r))).getD i 0 := by
  have ht := fun j hj => tabsG_ev h1 (tsCs ν r.size) 0 h j hj
  have hrb : ∀ l < nbN ν, (rbArr ν r).getD l 0 = r.getD (1 + l) 0 := fun l hl => by
    rw [rbArr, ofFn_getD, dif_pos hl]; rfl
  obtain ⟨h9, -⟩ := nbN_bounds ν
  simp only [tsE, tsT]
  refine ⟨?_, ?_, ?_⟩
  · rw [tabs9_a, ht 0 (by simp [tsCs])]
    congr 2
    simp only [tsCs, List.getD_cons_zero, List.map_map, Function.comp_def, cT_ev hi]
    exact (ofFn_eq_range (lo9 (rbArr ν r)) (fun l => r.getD (1 + l) 0) fun l => hrb l (by omega)).symm
  · rw [tabs9_b, ht 1 (by simp [tsCs])]
    congr 2
    simp only [tsCs, List.getD_cons_zero, List.getD_cons_succ, List.map_map, Function.comp_def, cT_ev hi]
    exact (ofFn_eq_range (hiN (nbN ν) (rbArr ν r)) (fun l => r.getD (1 + (9 + l)) 0) fun l => hrb (9 + l) (by omega)).symm
  · rw [ht 2 (by simp [tsCs])]
    congr 2
    rw [ofFn_eq_range (zLo r) (fun l => if h : l < 7 then pinnedRho ⟨l, h⟩ else r.getD 0 0) fun l => rfl]
    simp only [tsCs, List.getD_cons_zero, List.getD_cons_succ, List.map_map, Function.comp_def]
    refine List.map_congr_left fun l _ => ?_
    split_ifs
    · rw [ev_C, h1, mul_one]
    · exact cT_ev hi 0

set_option maxHeartbeats 4000000 in
/-- **The node kind `ν`'s `targetS` template computes `targetSNode4I ν`.** -/
theorem tplTS_ok (h1 : e.one = 1) (h : Eqns e (tplTS ν r.size).gates 0) :
    (tplTS ν r.size).outs.map (LinT.ev e) = (targetSNode4I ν r).toList := by
  simp only [tplTS, tplTSx, Eqns.append, mulsG_nlocs, tsRngG_nlocs, tsCtrG_nlocs, zero_add] at h
  rw [← mkCx_k0] at h
  obtain ⟨hT, hCh, hLa, hSt, hCA, hFi, hW, hRA, hRB, hRD, hRC, hC0, hC1, hC2, hC3, hG⟩ := h
  set T := tabs9 (nbN ν) (rbArr ν r) with hTdef
  have hE := tsE_ev hi h1 hT
  have hA : ∀ i, ((mkCx ν r.size).E 0 i).ev e = T.a i := fun i => by rw [mkCx_E]; exact (hE i).1
  have hB : ∀ i, ((mkCx ν r.size).E 1 i).ev e = T.b i := fun i => by rw [mkCx_E]; exact (hE i).2.1
  have hPA := tabs9_PA (n := nbN ν) (rbArr ν r)
  have hPB := tabs9_PB (n := nbN ν) (rbArr ν r)
  -- the point weights
  have vCh : ∀ σ < 2, (tsCh (mkCx ν r.size) σ).ev e = eq9 T (N4c.chBase ν σ) := fun σ hσ => by
    rw [tsCh, pL_ev (k := (mkCx ν r.size).k0) hCh, if_pos hσ, hA, hB]; rfl
  have vLa : ∀ σ < 2, (tsLa (mkCx ν r.size) σ).ev e = eq9 T (lastB ν σ) := fun σ hσ => by
    rw [tsLa, pL_ev (k := tsKLa (mkCx ν r.size)) hLa, if_pos hσ, hA, hB]; rfl
  have vSt : ∀ i < 3 * ν.vslots, (tsSt ν (mkCx ν r.size) i).ev e = eq9 T (N4c.stmtB ν + i) := fun i hi' => by
    rw [tsSt, pL_ev (k := tsKSt (mkCx ν r.size)) hSt, if_pos hi', hA, hB]; rfl
  have vCA : ∀ i < N4c.nAgg ν, (tsCA ν (mkCx ν r.size) i).ev e = eq9 T (N4c.cAB ν i) := fun i hi' => by
    rw [tsCA, pL_ev (k := tsKCA ν (mkCx ν r.size)) hCA, if_pos hi', hA, hB]; rfl
  have vFi : ∀ i < N4c.nAgg ν, ∀ t < tsM ν, (tsFi ν (mkCx ν r.size) i t).ev e = eq9 T (N4c.finB ν i + t) :=
    fun i hi' t ht => by
      have hb : i * tsM ν + t < N4c.nAgg ν * tsM ν := by nlinarith
      have hd : (i * tsM ν + t) / tsM ν = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
      have hm : (i * tsM ν + t) % tsM ν = t := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      rw [tsFi, if_pos ⟨hi', ht⟩, ev_L, mulsG_eqns (k := tsKFi ν (mkCx ν r.size)) hFi _ hb, hA, hB, hd, hm]; rfl
  have vW : ∀ σ < 2, ∀ o < 498, (tsW ν (mkCx ν r.size) σ o).ev e = eq9 T (N4c.wotsB ν σ + o) := fun σ hσ o ho => by
    rw [tsW, if_pos ⟨hσ, ho⟩, ev_L, mulsG_eqns (k := tsKW ν (mkCx ν r.size)) hW _ (by omega), hA, hB,
      show (498 * σ + o) / 498 = σ by omega, show (498 * σ + o) % 498 = o by omega]; rfl
  -- the range sums
  have vRA : ∀ σ < 2, (tsRngF (tsKRA ν (mkCx ν r.size)) σ).ev e = rangeI9 T (N4c.chBase ν σ + 1) (N4c.chLen ν σ - 2) :=
    fun σ hσ => tsRngF_ev hA hB hPA hPB (f := tsFA ν) (k := tsKRA ν (mkCx ν r.size)) hRA hσ
  have vRB : ∀ σ < 2, (tsRngF (tsKRB ν (mkCx ν r.size)) σ).ev e = rangeI9 T (N4c.wotsB ν σ + 400) 65 :=
    fun σ hσ => tsRngF_ev hA hB hPA hPB (f := tsFB ν) (k := tsKRB ν (mkCx ν r.size)) hRB hσ
  have vRD : ∀ σ < 2, (tsRngF (tsKRD ν (mkCx ν r.size)) σ).ev e = rangeI9 T (N4c.wotsB ν σ) 399 :=
    fun σ hσ => tsRngF_ev hA hB hPA hPB (f := tsFD ν) (k := tsKRD ν (mkCx ν r.size)) hRD hσ
  have vRC : ∀ i < N4c.nAgg ν, (tsRngF (tsKRC ν (mkCx ν r.size)) i).ev e = rangeI9 T (N4c.finB ν i) (ν.maxK - 1) :=
    fun i hi' => tsRngF_ev hA hB hPA hPB (f := tsFC ν) (k := tsKRC ν (mkCx ν r.size)) hRC hi'
  -- the class weights
  have vC : ∀ c < 10, (tsClsW ν (mkCx ν r.size) c).ev e = clsW ν (eq9 T) (rangeI9 T) c := by
    intro c hc
    interval_cases c <;> simp only [tsClsW, clsW, ev_append, sumG_ev, sumTo_eq]
    · exact Finset.sum_congr rfl fun x hx => vCh x (Finset.mem_range.1 hx)
    · exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx => vRA x (Finset.mem_range.1 hx))
        (Finset.sum_congr rfl fun x hx => vRB x (Finset.mem_range.1 hx))
    · exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx => vLa x (Finset.mem_range.1 hx))
        (Finset.sum_congr rfl fun x hx => vRC x (Finset.mem_range.1 hx))
    · exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx => vSt _ (by have := Finset.mem_range.1 hx; omega))
        (Finset.sum_congr rfl fun x hx => vCA x (Finset.mem_range.1 hx))
    · exact Finset.sum_congr rfl fun x hx => by
        rw [vSt _ (by have := Finset.mem_range.1 hx; omega), add_assoc]
    · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx => by
        rw [vSt _ (by have := Finset.mem_range.1 hx; omega), add_assoc])
        (Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun t ht => ?_)
      rw [vW x (Finset.mem_range.1 hx) _ (by have := Finset.mem_range.1 ht; omega), add_assoc]
    · exact Finset.sum_congr rfl fun x hx => vRD x (Finset.mem_range.1 hx)
    · exact Finset.sum_congr rfl fun x hx => vW x (Finset.mem_range.1 hx) _ (by norm_num)
    · exact Finset.sum_congr rfl fun x hx => vW x (Finset.mem_range.1 hx) _ (by norm_num)
    · refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun t ht => ?_
      rw [vW x (Finset.mem_range.1 hx) _ (by have := Finset.mem_range.1 ht; omega), add_assoc]
  -- the counter bits, the final blocks, `w43`
  have vK : ∀ (i : ℕ) (k : ℕ), Eqns e (tsCtrG ((mkCx ν r.size).E 0) ((mkCx ν r.size).E 1) (tsBLo ν i) (tsBN ν i)) k →
      ∀ j, (tsCtrO (tsBLo ν i) (tsBN ν i) k j).ev e = (ctrArr T (tsBLo ν i) (tsBN ν i)).getD j 0 :=
    fun i k hk j => by
      by_cases hj : j < 26
      · exact tsCtrO_ev hA hB hk hj
      · rw [ctrArr_getD_big _ _ _ (by omega), tsCtrO, if_neg hj]; rfl
  have vCT : ∀ j, (tsCT ν (mkCx ν r.size) j).ev e =
      (ctrArr T (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
        (ctrArr T (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
        ((ctrArr T (N4c.wotsB ν 0 + 400) 65).getD j 0 + (ctrArr T (N4c.wotsB ν 1 + 400) 65).getD j 0) :=
    fun j => by
      rw [tsCT, ev_append, ev_append, ev_append, vK 0 (tsKC0 ν (mkCx ν r.size)) hC0, vK 1 (tsKC1 ν (mkCx ν r.size)) hC1,
        vK 2 (tsKC2 ν (mkCx ν r.size)) hC2, vK 3 (tsKC3 ν (mkCx ν r.size)) hC3]
      rfl
  have vFG : ∀ j, (tsFinG ν (mkCx ν r.size) j).ev e = finG ν (eq9 T) j := fun j => by
    simp only [tsFinG, finG, ev_append, sumG_ev, ev_sc, sumTo_eq]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun x hx => ?_)
      (Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun t ht => ?_)
    · rw [vLa x (Finset.mem_range.1 hx), mul_comm]
    · rw [vFi x (Finset.mem_range.1 hx) t (Finset.mem_range.1 ht), mul_comm]
  have vWS : ∀ (sel : ℕ → ℕ) (b : ℕ), (tsW43 ν (mkCx ν r.size) sel b).ev e =
      NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) sel b +
        NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) sel b := fun sel b => by
    simp only [tsW43, NodeI.w43I, sumG_ev, sumTo_eq, sum_two']
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun o ho => ?_) (Finset.sum_congr rfl fun o ho => ?_) <;>
      (have ho := Finset.mem_range.1 ho
       rw [ite_ev_nil, ofFn_getD, dif_pos ho, vW _ (by norm_num) _ (by omega)])
  -- `G`
  have vG : ∀ p, (tsG ν (mkCx ν r.size) p).ev e = (gArr4 ν T).getD p 0 := fun p => by
    unfold tsG
    split_ifs with hp
    · have hW10 : ∀ c < 10, (Array.ofFn (n := 10) fun c => clsW ν (eq9 T) (rangeI9 T) c).getD c 0 =
          clsW ν (eq9 T) (rangeI9 T) c := fun c hc => by rw [ofFn_getD, dif_pos hc]
      simp only [gArr4]
      rw [ofFn_getD, dif_pos hp]
      unfold gAt4
      rw [hW10 0 (by norm_num), hW10 1 (by norm_num), hW10 2 (by norm_num), hW10 3 (by norm_num),
        hW10 4 (by norm_num), hW10 5 (by norm_num), hW10 6 (by norm_num), hW10 7 (by norm_num),
        hW10 8 (by norm_num), hW10 9 (by norm_num),
        ite_getD (1030 ≤ p ∧ p < 1056) (fun _ => by omega) (fun j : Fin 26 =>
            (ctrArr T (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD j 0 +
            (ctrArr T (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD j 0 +
            ((ctrArr T (N4c.wotsB ν 0 + 400) 65).getD j 0 + (ctrArr T (N4c.wotsB ν 1 + 400) 65).getD j 0))
          ((ctrArr T (N4c.chBase ν 0 + 1) (N4c.chLen ν 0 - 2)).getD (p - 1030) 0 +
            (ctrArr T (N4c.chBase ν 1 + 1) (N4c.chLen ν 1 - 2)).getD (p - 1030) 0 +
            ((ctrArr T (N4c.wotsB ν 0 + 400) 65).getD (p - 1030) 0 +
              (ctrArr T (N4c.wotsB ν 1 + 400) 65).getD (p - 1030) 0)) (fun _ => rfl),
        ite_getD (1024 ≤ p ∧ p < 1056) (fun _ => by omega) (fun j : Fin 32 => finG ν (eq9 T) j) (finG ν (eq9 T) (p - 1024)) (fun _ => rfl),
        ite_getD (584 ≤ p ∧ p < 592) (fun _ => by omega) (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) (· / 3) b +
            NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) (· / 3) b)
          (NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) (· / 3) (p - 584) +
            NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) (· / 3) (p - 584)) (fun _ => rfl),
        ite_getD (592 ≤ p ∧ p < 600) (fun _ => by omega) (fun b : Fin 8 => NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) (· % 3) b +
            NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) (· % 3) b)
          (NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 0 + o)) (· % 3) (p - 592) +
            NodeI.w43I (Array.ofFn (n := 399) fun o => eq9 T (N4c.wotsB ν 1 + o)) (· % 3) (p - 592)) (fun _ => rfl)]
      simp only [tsGAt, ev_append, ite_ev_nil, vC 0 (by norm_num), vC 1 (by norm_num), vC 2 (by norm_num),
        vC 3 (by norm_num), vC 4 (by norm_num), vC 5 (by norm_num), vC 6 (by norm_num), vC 7 (by norm_num),
        vC 8 (by norm_num), vC 9 (by norm_num), vCT, vFG, vWS]
    · simp only [gArr4]
      rw [ofFn_getD, dif_neg hp]; rfl
  -- the outputs
  have hM := mulsG_eqns (k := tsKG ν (mkCx ν r.size)) hG
  show ((List.range 64).map fun σ => sumG 19 fun hi => L (tsKG ν (mkCx ν r.size) + (σ * 19 + hi))).map (LinT.ev e) = _
  rw [List.map_map, targetSNode4I]
  simp only [Array.toList_ofFn]
  rw [ofFn_eq_range _ (fun σ => sumTo 19 fun hi => (eqTable (List.ofFn (zLo r))).getD hi 0 *
    (gArr4 ν T).getD (σ + 64 * hi) 0) fun σ => rfl]
  refine List.map_congr_left fun σ hσ => ?_
  have hσ := List.mem_range.1 hσ
  simp only [Function.comp, sumG_ev, sumTo_eq]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx := Finset.mem_range.1 hx
  rw [ev_L, hM _ (by omega), show (σ * 19 + x) % 19 = x by omega, show (σ * 19 + x) / 19 = σ by omega,
    mkCx_E, (hE _).2.2, vG]

end Proof

theorem tplTS_outs (ν : NodeKind) (a : ℕ) : (tplTS ν a).outs.length = 64 := by simp [tplTS, tplTSx]

end Tpl
end FR

end G6_FRVIRTplRepT
