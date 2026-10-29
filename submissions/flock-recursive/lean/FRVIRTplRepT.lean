-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).
import FRVIRTplRepLW
import FRVerifierImplNode4T

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

theorem mkCx_k0 (ν : NodeKind) (a : ℕ) : (mkCx ν a).k0 = nlocs (tsT ν a).1 := rfl

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
