-- New for lvm6 (WP-PHIV3, split off `Lvm6VPhiR3`): the class table `PT` with its kinds (affine kinds `AK`,
-- strided runs `SRunF`), the evaluator `PT.eval` off shared kernel tables, and its start-up check `ptCheck`.
import Lvm6VPhiR3
import Lvm6VPhiGK
import Lvm6VPhiBK
import Lvm6VPhiRK

/-!
# The class table and its evaluator

* Kernel tables: `sufT` (`eq(p.drop K, ·)`), `preT` (`eq(b.take e, ·)`), shared by every kind.
* `AK.valK`, **`AK.valK_eq`**; `PT` (classes, kinds `ak`, strided runs `str`, `rest`), `PT.kents`, `PT.kok`,
  `PT.kval`, **`kval_eq`**; **`PT.eval`**, **`eval_ents`**; `normL`; **`ptCheck`**, **`phiOk_pt`**,
  **`tw_typedPhase6_pt`**; `PT.ofCls` (a hint).
* PHIV7: **`PT.eval7`**, **`PT.eval7_eq`** (`= PT.eval` for every table and point), off the twins `AK.valK2`
  (`AK.valK2_eq`; powers hoisted, lines grouped), `CTpl.val2` (`CTpl.val2_eq`; singles grouped), `PT.kval7`,
  `PT.evalW7`; `hwB`, `lwB`, `eq_split11` (the word weight's split for the grouped singles).
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Shared kernel tables of the kinds -/

/-- A kernel lookup `(K, bound)` at `i`; past the bound `slow ()` (its list built only there). -/
@[inline] def klG (t : Array FE2 × ℕ) (i : ℕ) (slow : Unit → FE2) : FE2 := if i < t.2 then t.1.getD i 0 else slow ()

theorem klG_eq (t : Array FE2 × ℕ) (ρ : List FE2) (h : (t.1 = eqKernelAF ρ ∧ t.2 = 2 ^ ρ.length) ∨ t.2 = 0)
    (i : ℕ) : klG t i (fun _ => eqAtF ρ i) = eqAtF ρ i :=
  klF_eq t.1 t.2 ρ h i

/-- `eq(ρ.take k, i)` off a kernel table, the prefix built only past the bound. -/
@[inline] def ktG (kt : Array (Array FE2 × ℕ)) (ρ : List FE2) (k i : ℕ) : FE2 :=
  klG (kt.getD k (#[], 0)) i fun _ => eqAtF (ρ.take k) i

theorem ktG_eq (kt : Array (Array FE2 × ℕ)) (ρ : List FE2) (k i : ℕ) : ktG kt ρ k i = ktF kt ρ k i := rfl

/-- The kernels `kerF (f k)` for the `k < 22` in `ks` (others empty), with their bounds. -/
def segTab (f : ℕ → List FE2) (ks : List ℕ) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k => if k ∈ ks then (kerF (f k), 2 ^ (f k).length) else (#[], 0)).toArray

theorem segTab_ok (f : ℕ → List FE2) (ks : List ℕ) (k i : ℕ) :
    klG ((segTab f ks).getD k (#[], 0)) i (fun _ => eqAtF (f k) i) = eqAtF (f k) i := by
  apply klG_eq
  unfold segTab
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · exact Or.inl ⟨kerF_eq _, rfl⟩
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- A kernel with its bound. -/
def kpair (ρ : List FE2) (K : Array FE2) : Array FE2 × ℕ := (K, 2 ^ ρ.length)

theorem kpair_ok (ρ : List FE2) (K : Array FE2) (hK : K = kerF ρ) (i : ℕ) :
    klG (kpair ρ K) i (fun _ => eqAtF ρ i) = eqAtF ρ i :=
  klG_eq _ ρ (Or.inl ⟨by rw [kpair, hK, kerF_eq], rfl⟩) i

/-- The suffix segment of `p.drop K` in its own kernel: `p[K, 11)` for `K ≤ 11` (the rest off the kernel of
`p.drop 11`), else all of `p.drop K`. -/
def sfSeg (p : List FE2) (K : ℕ) : List FE2 := if K ≤ 11 then (p.drop K).take (11 - K) else p.drop K

/-- **`eq(p.drop K, v)` off kernels** (`st` the suffix kernels, `hi` the kernel of `p.drop 11` with its bound):
one product for `K ≤ 11`, none past it. -/
@[inline] def sufT (p : List FE2) (st : Array (Array FE2 × ℕ)) (hi : Array FE2 × ℕ) (K v : ℕ) : FE2 :=
  let t := st.getD K (#[], 0)
  if K ≤ 11 then
    let s := 2 ^ (11 - K)
    mulE (klG t (v % s) fun _ => eqAtF (sfSeg p K) (v % s)) (klG hi (v / s) fun _ => eqAtF (p.drop 11) (v / s))
  else klG t v fun _ => eqAtF (sfSeg p K) v

/-- PHIV4: `kerTabS` with the prefix-`12` kernel one step off `K11` (`2^11` products, not `2^12`). -/
def kerTabS2 (ρ : List FE2) (ks : List ℕ) (K11 : Array FE2) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k =>
    if k ∈ ks then (if k = 11 then K11 else if k = 12 ∧ 12 ≤ ρ.length then kerStep K11 (ρ.getD 11 0)
      else kerF (ρ.take k), 2 ^ (ρ.take k).length) else (#[], 0)).toArray

theorem kerF_take_succ (ρ : List FE2) (k : ℕ) (hk : k < ρ.length) :
    kerF (ρ.take (k + 1)) = kerStep (kerF (ρ.take k)) (ρ.getD k 0) := by
  unfold kerF
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem ktFS2_eq (ρ : List FE2) (ks : List ℕ) (K11 : Array FE2) (hK : K11 = kerF (ρ.take 11)) (k i : ℕ) :
    ktF (kerTabS2 ρ ks K11) ρ k i = eqAtF (ρ.take k) i := by
  apply klF_eq
  unfold kerTabS2
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · left
      refine ⟨?_, rfl⟩
      split
      · rename_i h11; subst h11; rw [hK, kerF_eq]
      · split
        · rename_i h12
          obtain ⟨rfl, h12⟩ := h12
          rw [hK, ← kerF_take_succ ρ 11 (by omega), kerF_eq]
        · exact kerF_eq _
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- PHIV4: `sufT` as a low and a high factor (`sufT_split`), for the grouped finals (`SRunF.valG`). -/
def sufM (K : ℕ) : ℕ := if K ≤ 11 then 2 ^ (11 - K) else 1

@[inline] def sufL (p : List FE2) (st : Array (Array FE2 × ℕ)) (K u : ℕ) : FE2 :=
  if K ≤ 11 then klG (st.getD K (#[], 0)) u (fun _ => eqAtF (sfSeg p K) u) else 1

@[inline] def sufH (p : List FE2) (st : Array (Array FE2 × ℕ)) (hi : Array FE2 × ℕ) (K w : ℕ) : FE2 :=
  if K ≤ 11 then klG hi w (fun _ => eqAtF (p.drop 11) w) else klG (st.getD K (#[], 0)) w (fun _ => eqAtF (sfSeg p K) w)

theorem sufT_split (p : List FE2) (st : Array (Array FE2 × ℕ)) (hi : Array FE2 × ℕ) (K v : ℕ) :
    sufT p st hi K v = sufL p st K (v % sufM K) * sufH p st hi K (v / sufM K) := by
  unfold sufT sufL sufH sufM
  by_cases hK : K ≤ 11
  · simp only [hK, ↓reduceIte, mulE_eq]
  · simp only [hK, ↓reduceIte, Nat.div_one, one_mul]

theorem sufT_eq (p : List FE2) (ks : List ℕ) (H : Array FE2) (hp : 11 ≤ p.length) (hH : H = kerF (p.drop 11))
    (K v : ℕ) : sufT p (segTab (sfSeg p) ks) (kpair (p.drop 11) H) K v = eqAtF (p.drop K) v := by
  unfold sufT
  dsimp only
  simp only [segTab_ok (sfSeg p) ks K, kpair_ok _ H hH]
  split
  · rename_i hK
    rw [mulE_eq, show sfSeg p K = (p.drop K).take (11 - K) from if_pos hK]
    have hl : ((p.drop K).take (11 - K)).length = 11 - K := by simp; omega
    have hd : (p.drop K).drop (11 - K) = p.drop 11 := by simp only [List.drop_drop]; congr 1; omega
    conv_rhs => rw [← List.take_append_drop (11 - K) (p.drop K), eqAtF_append, hl, hd]
    rw [show v % 2 ^ (11 - K) = v % 2 ^ ((p.drop K).take (11 - K)).length by rw [hl], ← eqAtF_mod]
  · rename_i hK
    rw [show sfSeg p K = p.drop K from if_neg hK]

/-- `eq(b.take e, u)`: `1` at `e = 0`, off the twin-word kernels `kb` for `e ≤ 12`, else directly. -/
@[inline] def preB (b : List FE2) (kb : Array (Array FE2 × ℕ)) (e u : ℕ) : FE2 :=
  if e = 0 then 1
  else if e ≤ 12 then
    mulE (if u % 2 = 1 then b.headD 0 else 1 + b.headD 0) (klG (kb.getD e (#[], 0)) (u / 2) fun _ =>
      eqAtF (b.take e).tail (u / 2))
  else eqAtF (b.take e) u

theorem preB_eq (b : List FE2) (kb : Array (Array FE2 × ℕ)) (hb : b ≠ [])
    (hkb : ∀ j i, klF (kb.getD j (#[], 0)).1 (kb.getD j (#[], 0)).2 (b.take j).tail i = eqAtF (b.take j).tail i)
    (e u : ℕ) : preB b kb e u = eqAtF (b.take e) u := by
  have hkb' : klG (kb.getD e (#[], 0)) (u / 2) (fun _ => eqAtF (b.take e).tail (u / 2)) =
      eqAtF (b.take e).tail (u / 2) := hkb e (u / 2)
  unfold preB
  split
  · rename_i h; subst h; simp
  · split
    · rename_i h0 _
      rw [hkb', mulE_eq]
      obtain ⟨b0, bt, rfl⟩ := List.exists_cons_of_ne_nil hb
      rw [show e = (e - 1) + 1 by omega, List.take_succ_cons, eqAtF_succ]
      simp
    · rfl

/-- The middle segment `b[11, e)` of a long prefix. -/
def midSeg (b : List FE2) (e : ℕ) : List FE2 := (b.drop 11).take (e - 11)

/-- **`eq(b.take e, u)` off kernels**: `preB` for `e ≤ 12`, else the prefix-11 kernel `B11` times the kernel of
`b[11, e)` (`mt`): one product. -/
@[inline] def preT (b : List FE2) (kb mt : Array (Array FE2 × ℕ)) (B11 : Array FE2) (e u : ℕ) : FE2 :=
  if e ≤ 12 then preB b kb e u
  else mulE (B11.getD (u % 2048) 0) (klG (mt.getD e (#[], 0)) (u / 2048) fun _ => eqAtF (midSeg b e) (u / 2048))

theorem preT_eq (b : List FE2) (kb : Array (Array FE2 × ℕ)) (es : List ℕ) (B11 : Array FE2) (hb : 11 ≤ b.length)
    (hkb : ∀ j i, klF (kb.getD j (#[], 0)).1 (kb.getD j (#[], 0)).2 (b.take j).tail i = eqAtF (b.take j).tail i)
    (hB : B11 = kerF (b.take 11)) (e u : ℕ) :
    preT b kb (segTab (midSeg b) es) B11 e u = eqAtF (b.take e) u := by
  have hbne : b ≠ [] := by intro h; rw [h] at hb; simp at hb
  unfold preT
  split
  · exact preB_eq b kb hbne hkb e u
  · rename_i he
    subst hB
    have hl : (b.take 11).length = 11 := by simp; omega
    rw [segTab_ok (midSeg b) es e, mulE_eq, kerF_getD _ _ (by rw [hl]; exact Nat.mod_lt _ (by norm_num))]
    have h1 : (b.take e).take 11 = b.take 11 := by rw [List.take_take]; congr 1; omega
    have h2 : (b.take e).drop 11 = midSeg b e := by rw [midSeg, List.drop_take]
    rw [← eq_ysplit (b.take e) 11 u (by simp; omega), h1, h2]
    rfl

/-! ## The table and its evaluation -/

/-- **The class table**: the classes and the other entries. -/
structure PT where
  cls : Array CTpl
  rest : RCov
  /-- PHIV2: the affine kinds (loop classes, aligned externals). -/
  ak : Array AK
  /-- PHIV3: the strided runs (STR's factored carry automaton). -/
  str : Array SRunF
  /-- PHIV3: the gather kinds (loop entries off the shared slot kernel). -/
  gk : Array GK
  /-- PHIV6: the `BITS` kinds (bit templates in closed form, `Lvm6VPhiBK`). -/
  bk : Array BKB
  /-- ST-4: the row kind (rows under no class, class differences; `Lvm6VPhiRK`). -/
  rk : RK

/-- **The kinds' entries** (the extension point: a new kind adds its expansion here, its check to `PT.kok`, its
value to `PT.kval`, and its case to `kval_eq`). -/
def PT.kents (P : PT) : List Q4 :=
  P.ak.toList.flatMap AK.ents ++ P.str.toList.flatMap SRunF.ents ++ P.gk.toList.flatMap GK.ents ++
    P.bk.toList.flatMap BKB.ents

/-- The kinds' start-up checks. -/
def PT.kok (P : PT) : Bool := P.ak.toList.all AK.okB && P.str.toList.all SRunF.okB && P.gk.toList.all GK.okB &&
  P.bk.toList.all BKB.okB

/-- **Its entries.** -/
def PT.ents (P : PT) : List Q4 := P.cls.toList.flatMap CTpl.ents ++ P.kents ++ P.rest.ents ++ P.rk.ents

/-- The table check: every class and every kind is aligned and fits. -/
def PT.okB (P : PT) : Bool := P.cls.toList.all CTpl.okB && P.kok

/-- An entry's `(c, idx)`. -/
def toIdx (q : Q4) : FE2 × ℕ := (q.1, idxOf q.2.1 q.2.2.1 q.2.2.2)

/-- The aligned twin factor of a word point `b = b₀ :: _`. -/
def twT (b : List FE2) : FE2 := (1 + b.headD 0) + xF * b.headD 0

theorem twin_al (l : List FE2) (hl : l ≠ []) (c : ℕ) :
    eqAtF l (2 * c) + xF * eqAtF l (2 * c + 1) = twT l * eqAtF l.tail c := by
  obtain ⟨b0, bt, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [eqAtF_succ, eqAtF_succ, if_neg (by omega), if_pos (by omega), show 2 * c / 2 = c by omega,
    show (2 * c + 1) / 2 = c by omega]
  simp only [twT, List.headD_cons, List.tail_cons]
  ring

/-- The twin-word kernels `eq((b.take k).tail, ·)` for the `k` in `ks`. -/
def kbTab (b : List FE2) (ks : List ℕ) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k =>
    if k ∈ ks then (kerF (b.take k).tail, 2 ^ (b.take k).tail.length) else (#[], 0)).toArray

theorem kbTab_ok (b : List FE2) (ks : List ℕ) (k i : ℕ) :
    klF ((kbTab b ks).getD k (#[], 0)).1 ((kbTab b ks).getD k (#[], 0)).2 (b.take k).tail i =
      eqAtF (b.take k).tail i := by
  apply klF_eq
  unfold kbTab
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · exact Or.inl ⟨kerF_eq _, rfl⟩
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- `kbTab` with the prefix-`12` twin kernel given (`mkSEqF b.tail`'s low table). -/
def kbTabS (b : List FE2) (ks : List ℕ) (B12 : Array FE2) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k =>
    if k ∈ ks then (if k = 12 then B12 else kerF (b.take k).tail, 2 ^ (b.take k).tail.length) else (#[], 0)).toArray

theorem kbTabS_ok (b : List FE2) (ks : List ℕ) (B12 : Array FE2) (hB : B12 = kerF (b.take 12).tail) (k i : ℕ) :
    klF ((kbTabS b ks B12).getD k (#[], 0)).1 ((kbTabS b ks B12).getD k (#[], 0)).2 (b.take k).tail i =
      eqAtF (b.take k).tail i := by
  apply klF_eq
  unfold kbTabS
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · left
      refine ⟨?_, rfl⟩
      split
      · rename_i h12; subst h12; rw [hB, kerF_eq]
      · exact kerF_eq _
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- PHIV5: `(Σ_{j<e} eq(ms, j), eq(ms, e))` by the bits of `e`, at most two products a level (`wPreH`'s form with
the factors `(1 + m, m)`, whose sum is `1`). -/
def sumPre : List FE2 → ℕ → FE2 × FE2
  | m0 :: ms, e =>
    let r := sumPre ms (e / 2)
    (r.1 + (if e % 2 = 1 then mulE (1 + m0) r.2 else 0), mulE (if e % 2 = 1 then m0 else 1 + m0) r.2)
  | [], e => (if e = 0 then 0 else 1, 1)

theorem sumPre_eq : ∀ (ms : List FE2) (e : ℕ), e ≤ 2 ^ ms.length →
    sumPre ms e = (((List.range e).map (eqAtF ms)).sum, eqAtF ms e)
  | [], e, he => by
    have : e = 0 ∨ e = 1 := by simp at he; omega
    rcases this with rfl | rfl <;> simp [sumPre]
  | m0 :: ms, e, he => by
    have hq : e / 2 ≤ 2 ^ ms.length := by
      simp only [List.length_cons, pow_succ] at he; omega
    have h1 : (1 + m0) + m0 = 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [sumPre, sumPre_eq ms (e / 2) hq, show eqAtF (m0 :: ms) =
      (fun x => (if x % 2 = 1 then m0 else 1 + m0) * eqAtF ms (x / 2)) from funext fun x => eqAtF_succ m0 ms x]
    simp only [mulE_eq]
    obtain ⟨q, rfl | rfl⟩ : ∃ q, e = 2 * q ∨ e = 2 * q + 1 := ⟨e / 2, by omega⟩
    · have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      rw [sum_range_pairG (eqAtF ms) (1 + m0) m0 q, h1, one_mul]
      simp only [e1, e2, show (0 : ℕ) ≠ 1 from by decide, ite_false, add_zero]
    · have e3 : (2 * q + 1) % 2 = 1 := by omega
      have e4 : (2 * q + 1) / 2 = q := by omega
      have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      rw [range_add1 (2 * q), List.map_append, List.sum_append, sum_range_pairG (eqAtF ms) (1 + m0) m0 q, h1,
        one_mul]
      simp only [e1, e2, e3, e4, ite_true, show (0 : ℕ) ≠ 1 from by decide, ite_false, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]

/-- PHIV5: `clsCombF` with the fixed-word instance sum `Σ_{j<n} eq(XL, j)` in closed form (`sumPre`, `O(L)`
products; was a kernel of `2^L`). -/
def clsCombF2 (n : ℕ) (XL YL : List FE2) (XH YH V0 V1 V2 : FE2) : FE2 :=
  let D0 := if XL.length = YL.length ∧ n ≤ 2 ^ XL.length then (wPreH (hzip XL YL) n).1
    else dotN (eqAtF XL) (eqAtF YL) n
  let D1 := if V1 = 0 then 0 else
    let XK := kerF XL
    let YK := kerF YL
    ((List.range' 1 (n - 1)).map fun j =>
      mulE (klF XK (2 ^ XL.length) XL j) (klF YK (2 ^ YL.length) YL (j - 1))).sum
  let D2 := if V2 = 0 then 0 else if n ≤ 2 ^ XL.length then (sumPre XL n).1 else sumN (eqAtF XL) n
  mulE XH (mulE YH (mulE D0 V0 + mulE D1 V1) + mulE D2 V2)

theorem clsCombF2_eq (n : ℕ) (XL YL : List FE2) (XH YH V0 V1 V2 : FE2) :
    clsCombF2 n XL YL XH YH V0 V1 V2 = clsCombF n XL YL XH YH V0 V1 V2 := by
  have hD2 : (if V2 = 0 then 0 else if n ≤ 2 ^ XL.length then (sumPre XL n).1 else sumN (eqAtF XL) n) =
      (if V2 = 0 then 0 else sumN (fun j => klF (kerF XL) (2 ^ XL.length) XL j) n) := by
    have hX : (fun j => klF (kerF XL) (2 ^ XL.length) XL j) = eqAtF XL :=
      funext fun j => klF_eq _ _ _ (Or.inl ⟨kerF_eq _, rfl⟩) j
    rw [hX]
    split
    · rfl
    · split
      · rename_i h; rw [sumPre_eq _ _ h]; rfl
      · rfl
  simp only [clsCombF2, clsCombF]
  rw [hD2]

/-- A class's value at a point (`ka`, `kb`: kernel tables of the slot and twin-word prefixes; `fcvR`, `fovR`,
`fwR`: the word weights of the fixed words). -/
@[specialize] def CTpl.val (k : CTpl) (fa : ℕ → FE2) (m b : List FE2) (ka kb : Array (Array FE2 × ℕ))
    (fcvR fwR : ℕ → FE2) : FE2 :=
  let T := twT b
  let bt := b.take k.bb
  let b0 := b.headD 0
  let xlo : ℕ → FE2 := fun i => ktF ka m k.a i
  let ytl : ℕ → FE2 := fun c => klF (kb.getD k.bb (#[], 0)).1 (kb.getD k.bb (#[], 0)).2 bt.tail c
  let ylo : ℕ → FE2 := fun w => mulE (if w % 2 = 1 then b0 else 1 + b0) (ytl (w / 2))
  let yod : ℕ → FE2 := fun c => ylo (2 * c + 1) + KT.mX (ylo (2 * c + 2))
  clsCombF2 k.n ((m.drop k.a).take k.L) ((b.drop k.bb).take k.L) (k.XH m) (k.YH b)
    (rsum k.t0 fa T xlo ytl yod ylo (m.take k.a) bt.tail) (rsum k.t1 fa T xlo ytl yod ylo (m.take k.a) bt.tail)
    (rsum k.t2 fa T xlo fcvR (fun c => fwR (2 * c + 1) + KT.mX (fwR (2 * c + 2))) fwR (m.take k.a) b.tail)

/-- PHIV7: `CTpl.val` with the singles grouped (`rsumK`): in `t0`, `t1` by `(o, y % 2)` (the twin-word factor
`b0` or `1 + b0` once per group), in `t2` by `(o, y / 2048)` with `fwR y = hwR (y / 2048) · lwR y`. -/
@[specialize] def CTpl.val2 (k : CTpl) (fa : ℕ → FE2) (m b : List FE2) (ka kb : Array (Array FE2 × ℕ))
    (fcvR fwR hwR lwR : ℕ → FE2) : FE2 :=
  let T := twT b
  let bt := b.take k.bb
  let b0 := b.headD 0
  let xt := ka.getD k.a (#[], 0)
  let yt := kb.getD k.bb (#[], 0)
  let xlo : ℕ → FE2 := fun i => klF xt.1 xt.2 (m.take k.a) i
  let ytl : ℕ → FE2 := fun c => klF yt.1 yt.2 bt.tail c
  let ylo : ℕ → FE2 := fun w => mulE (if w % 2 = 1 then b0 else 1 + b0) (ytl (w / 2))
  let yod : ℕ → FE2 := fun c => ylo (2 * c + 1) + KT.mX (ylo (2 * c + 2))
  let hw0 : ℕ → FE2 := fun q => if q = 1 then b0 else 1 + b0
  let lw0 : ℕ → FE2 := fun w => ytl (w / 2)
  clsCombF2 k.n ((m.drop k.a).take k.L) ((b.drop k.bb).take k.L) (k.XH m) (k.YH b)
    (rsumK k.t0 fa T xlo ytl yod ylo (m.take k.a) bt.tail (· % 2) hw0 lw0)
    (rsumK k.t1 fa T xlo ytl yod ylo (m.take k.a) bt.tail (· % 2) hw0 lw0)
    (rsumK k.t2 fa T xlo fcvR (fun c => fwR (2 * c + 1) + KT.mX (fwR (2 * c + 2))) fwR (m.take k.a) b.tail (· / 2048)
      hwR lwR)

theorem CTpl.val2_eq (k : CTpl) (fa : ℕ → FE2) (m b : List FE2) (ka kb : Array (Array FE2 × ℕ))
    (fcvR fwR hwR lwR : ℕ → FE2) (h : ∀ y, fwR y = hwR (y / 2048) * lwR y) :
    k.val2 fa m b ka kb fcvR fwR hwR lwR = k.val fa m b ka kb fcvR fwR := by
  unfold CTpl.val2 CTpl.val
  dsimp only
  rw [rsumK_eq k.t0 _ _ _ _ _ _ _ _ _ _ _ ?h0, rsumK_eq k.t1 _ _ _ _ _ _ _ _ _ _ _ ?h1,
    rsumK_eq k.t2 _ _ _ _ _ _ _ _ _ _ _ h]
  · rfl
  case h0 => exact fun w => mulE_eq _ _
  case h1 => exact fun w => mulE_eq _ _

/-- PHIV7: the high factor of a word's weight, `eq(b.drop 11, q)` off its kernel. -/
@[inline] def hwB (b : List FE2) (BH : Array FE2) (q : ℕ) : FE2 :=
  klG (kpair (b.drop 11) BH) q (fun _ => eqAtF (b.drop 11) q)

/-- PHIV7: the low factor of a word's weight, `eq(b.take 11, y % 2048)` off its kernel. -/
@[inline] def lwB (B11 : Array FE2) (y : ℕ) : FE2 := B11.getD (y % 2048) 0

/-- PHIV7: **a word's weight off the split kernels**: `eq(b, y) = eq(b.drop 11, y / 2048) · eq(b.take 11, y % 2048)`. -/
theorem eq_split11 (b : List FE2) (hb : 11 ≤ b.length) (B11 BH : Array FE2) (hB11 : B11 = kerF (b.take 11))
    (hBH : BH = kerF (b.drop 11)) (y : ℕ) : eqAtF b y = hwB b BH (y / 2048) * lwB B11 y := by
  have hl : (b.take 11).length = 11 := by simp; omega
  rw [hwB, lwB, kpair_ok _ _ hBH, hB11, kerF_getD _ _ (by rw [hl]; exact Nat.mod_lt _ (by norm_num)), mul_comm,
    ← eq_ysplit b 11 y hb]
  rfl

/-- PHIV5: `AK.S` in closed form (`sumPre`: `O(L)` products, was `n·L`). -/
def AK.SF (k : AK) (m : List FE2) : FE2 :=
  if k.n = 2 ^ (k.XL m).length then 1
  else if k.n ≤ 2 ^ (k.XL m).length then (sumPre (k.XL m) k.n).1 else sumN (eqAtF (k.XL m)) k.n

theorem AK.SF_eq (k : AK) (m : List FE2) : k.SF m = k.S m := by
  by_cases h1 : k.n = 2 ^ (k.XL m).length
  · simp only [AK.SF, AK.S, h1, ↓reduceIte]
  · by_cases h2 : k.n ≤ 2 ^ (k.XL m).length
    · simp only [AK.SF, AK.S, h1, h2, ↓reduceIte]
      rw [sumPre_eq _ _ h2]
      rfl
    · simp only [AK.SF, AK.S, h1, h2, ↓reduceIte]

/-- **An affine kind's value off the shared kernel tables** (`ka`, `kb`: slot and twin-word prefixes; `mt`: the
middle segments `b[11, e)`; `sm`, `sb`: the suffix kernels of `m`, `b`; `B11`: the kernel of `b.take 11`; `MH`,
`BH`: the kernels of `m.drop 11`, `b.drop 11` with their bounds). A strided entry's word weight is two lookups and
at most two products. -/
@[specialize] def AK.valK (k : AK) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 : Array FE2) (MH BH : Array FE2 × ℕ) : FE2 :=
  let K := k.a + k.L
  k.valW fa fw (fun x => mulE (ktG ka m k.a (x % 2 ^ k.a)) (sufT m sm MH K (x / 2 ^ K)))
    (fun i y =>
      let e := k.ds.getD i 0
      mulE (preT b kb mt B11 e (y % 2 ^ e)) (sufT b sb BH (e + k.L) (y / 2 ^ (e + k.L))))
    (k.SF m) (k.ds.map (k.D m b)) (k.D m b)

theorem AK.valK_eq (k : AK) (hok : k.okB = true) (fa : ℕ → FE2) (m b : List FE2) (hm : m.length = 20)
    (hb : b.length = 21) (fw : ℕ → FE2) (hfw : ∀ y, fw y = eqAtF b y) (ka kb : Array (Array FE2 × ℕ))
    (hka : ∀ j i, ktF ka m j i = eqAtF (m.take j) i)
    (hkb : ∀ j i, klF (kb.getD j (#[], 0)).1 (kb.getD j (#[], 0)).2 (b.take j).tail i = eqAtF (b.take j).tail i)
    (kse ksm ksb : List ℕ) (B11 MH BH : Array FE2) (hB11 : B11 = kerF (b.take 11)) (hMH : MH = kerF (m.drop 11))
    (hBH : BH = kerF (b.drop 11)) :
    k.valK fa m b fw ka kb (segTab (midSeg b) kse) (segTab (sfSeg m) ksm) (segTab (sfSeg b) ksb) B11
      (kpair (m.drop 11) MH) (kpair (b.drop 11) BH) = (k.ents.map (qv fa (eqAtF m) (eqAtF b))).sum := by
  unfold AK.valK
  dsimp only
  refine k.valW_eq fa m b hok hm hb _ _ _ _ _ _ hfw (fun x => ?_) (fun i y => ?_) (k.SF_eq m) rfl rfl
  · rw [ktG_eq, hka, sufT_eq m ksm MH (by omega) hMH, mulE_eq]
    unfold AK.MX
    simp only [List.drop_drop]
  · rw [preT_eq b kb kse B11 (by omega) hkb hB11, sufT_eq b ksb BH (by omega) hBH, mulE_eq]
    unfold AK.WY
    simp only [List.drop_drop]

/-- PHIV7: `sufT` with `s = 2^(11 - K)` given (computed once per kind, not per entry). -/
@[inline] def sufTs (p : List FE2) (st : Array (Array FE2 × ℕ)) (hi : Array FE2 × ℕ) (K s v : ℕ) : FE2 :=
  let t := st.getD K (#[], 0)
  if K ≤ 11 then
    mulE (klG t (v % s) fun _ => eqAtF (sfSeg p K) (v % s)) (klG hi (v / s) fun _ => eqAtF (p.drop 11) (v / s))
  else klG t v fun _ => eqAtF (sfSeg p K) v

/-- PHIV7: a word stride's constants `e`, `2^e`, `e + L`, `2^(e + L)`, `2^(11 - (e + L))`. -/
structure AKS where
  e : ℕ
  pe : ℕ
  q : ℕ
  pq : ℕ
  s : ℕ

/-- The constants of the stride `2^e` of a kind with `L` instance bits. -/
def AKS.of (L e : ℕ) : AKS := ⟨e, 2 ^ e, e + L, 2 ^ (e + L), 2 ^ (11 - (e + L))⟩

theorem getD_map_of {α β : Type} (a : Array α) (f : α → β) (i : ℕ) (d : α) :
    (a.map f).getD i (f d) = f (a.getD i d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Option.getD_map]

/-- PHIV7: **`AK.valK` with the powers hoisted** (per kind, and per stride in `AKS.of`) and the lines grouped
(`AK.valW2`): a strided word's weight is `preT` of its low bits (per line) times `sufTs` of its high part (per
group). -/
@[specialize] def AK.valK2 (k : AK) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 : Array FE2) (MH BH : Array FE2 × ℕ) : FE2 :=
  let K := k.a + k.L
  let pa := 2 ^ k.a
  let pK := 2 ^ K
  let sK := 2 ^ (11 - K)
  let cs := k.ds.map (AKS.of k.L)
  let c0 := AKS.of k.L 0
  let Dv := k.ds.map (k.D m b)
  let nd := k.ds.size
  let fdw := ((List.range (4 * nd)).map fun j => mulE (fa (j % 4)) (rd Dv k.ds (k.D m b) (j / 4))).toArray
  k.valW2 fa fw (fun x => mul1 (ktG ka m k.a (x % pa)) (sufTs m sm MH K sK (x / pK)))
    (fun o i => if o < 4 ∧ i < nd then fdw.getD (4 * i + o) 0 else mulE (fa o) (rd Dv k.ds (k.D m b) i))
    (fun i y => let c := cs.getD i c0; preT b kb mt B11 c.e (y % c.pe))
    (fun i y => y / (cs.getD i c0).pq)
    (fun i h => let c := cs.getD i c0; sufTs b sb BH c.q c.s h)
    (k.SF m)

theorem AK.valK2_eq (k : AK) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 : Array FE2) (MH BH : Array FE2 × ℕ) :
    k.valK2 fa m b fw ka kb mt sm sb B11 MH BH = k.valK fa m b fw ka kb mt sm sb B11 MH BH := by
  unfold AK.valK2 AK.valK
  dsimp only
  rw [AK.valW2_eq k _ _ _ _ (fun i y => mulE (preT b kb mt B11 (k.ds.getD i 0) (y % 2 ^ k.ds.getD i 0))
    (sufT b sb BH (k.ds.getD i 0 + k.L) (y / 2 ^ (k.ds.getD i 0 + k.L)))) _ _ _ _ _ _ ?hw ?hfaw]
  · congr 1
    funext x
    rw [mul1_eq, mulE_eq]
    rfl
  · intro i y
    simp only [getD_map_of]
    rw [mulE_eq]
    rfl
  · intro o i
    split
    · rename_i h
      rw [getD_mapRange _ _ _ _ (by omega), mulE_eq,
        show (4 * i + o) % 4 = o by omega, show (4 * i + o) / 4 = i by omega]
    · exact mulE_eq _ _

/-- **The kinds' value** off the shared kernel tables: affine kinds, strided runs (finals' weights
`eq(b.drop n, ·)` by `sufT`), gather kinds. -/
@[specialize] def PT.kval (P : PT) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 MH BH : Array FE2) : FE2 :=
  let MHp := kpair (m.drop 11) MH
  let BHp := kpair (b.drop 11) BH
  P.ak.foldl (fun s k => s + k.valK fa m b fw ka kb mt sm sb B11 MHp BHp) 0 +
    P.str.foldl (fun s F => s + F.valGS fa (sufT m sm MHp (F.p + F.n)) (sufL b sb F.n) (sufH b sb BHp F.n)
      (sufM F.n) m b) 0 +
    P.gk.foldl (fun s g => s + g.valW fa (ktG ka m g.l) (sufT m sm MHp g.l) (fun w => B11.getD w 0)
      (fun v => klG BHp v fun _ => eqAtF (b.drop 11) v)) 0 +
    P.bk.foldl (fun s k => s + k.valW fa m b) 0

theorem kval_eq (P : PT) (hok : P.kok = true) (fa : ℕ → FE2) (m b : List FE2) (hm : m.length = 20)
    (hb : b.length = 21) (fw : ℕ → FE2) (hfw : ∀ y, fw y = eqAtF b y) (ka kb : Array (Array FE2 × ℕ))
    (hka : ∀ j i, ktF ka m j i = eqAtF (m.take j) i)
    (hkb : ∀ j i, klF (kb.getD j (#[], 0)).1 (kb.getD j (#[], 0)).2 (b.take j).tail i = eqAtF (b.take j).tail i)
    (kse ksm ksb : List ℕ) (B11 MH BH : Array FE2) (hB11 : B11 = kerF (b.take 11)) (hMH : MH = kerF (m.drop 11))
    (hBH : BH = kerF (b.drop 11)) :
    P.kval fa m b fw ka kb (segTab (midSeg b) kse) (segTab (sfSeg m) ksm) (segTab (sfSeg b) ksb) B11 MH BH =
      (P.kents.map (qv fa (eqAtF m) (eqAtF b))).sum := by
  simp only [PT.kok, Bool.and_eq_true, List.all_eq_true] at hok
  unfold PT.kval PT.kents
  dsimp only
  rw [← Array.foldl_toList, foldl_add_eq, zero_add, ← Array.foldl_toList, foldl_add_eq, zero_add,
    ← Array.foldl_toList, foldl_add_eq, zero_add, ← Array.foldl_toList, foldl_add_eq, zero_add, List.map_append,
    List.map_append, List.map_append, List.sum_append, List.sum_append, List.sum_append, sum_map_flatMap,
    sum_map_flatMap, sum_map_flatMap, sum_map_flatMap]
  obtain ⟨hok, hokB⟩ := hok
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg List.sum (List.map_congr_left fun k hk => ?_))
    (congrArg List.sum (List.map_congr_left fun F hF => ?_))) (congrArg List.sum (List.map_congr_left fun g hg => ?_)))
    (congrArg List.sum (List.map_congr_left fun k hk => k.valW_eq (hokB k hk) fa m b hm hb))
  · exact k.valK_eq (hok.1.1 k hk) fa m b hm hb fw hfw ka kb hka hkb kse ksm ksb B11 MH BH hB11 hMH hBH
  · exact (F.valGS_eq (hok.1.2 F hF) fa _ _ _ _ m b hm (fun z => sufT_eq m ksm MH (by omega) hMH _ z)).trans
      ((F.valG_eq fa _ _ (sufT b _ (kpair (b.drop 11) BH) F.n) _ m b (fun z => sufT_split b _ _ F.n z)).trans
      (F.valT_eq (hok.1.2 F hF) fa _ m b hm hb (fun z => sufT_eq b ksb BH (by omega) hBH F.n z)))
  · exact g.valW_eq (hok.2 g hg) fa m b hm hb _ _ _ _ (fun i => (ktG_eq ka m g.l i).trans (hka g.l i))
      (sufT_eq m ksm MH (by omega) hMH g.l) (fun w hw => by rw [hB11]; exact kerF_getD _ _ (by simpa [hb] using hw))
      (fun v => kpair_ok (b.drop 11) BH hBH v)

/-- The evaluation with its weights given. -/
@[specialize] def PT.evalW (P : PT) (m b : List FE2) (fa fs fcv fw : ℕ → FE2) (K11 B12 B11 MH BH : Array FE2) :
    FE2 :=
  let ka := kerTabS2 m (P.cls.toList.map CTpl.a ++ (P.ak.toList.filterMap fun k => if k.a ≤ 11 then some k.a else none)
    ++ P.gk.toList.map GK.l) K11
  let kb := kbTabS b (P.cls.toList.map CTpl.bb ++ P.ak.toList.flatMap fun k => k.ds.toList.filter (· ≤ 12)) B12
  let mt := segTab (midSeg b) (P.ak.toList.flatMap fun k => k.ds.toList.filter (12 < ·))
  let sm := segTab (sfSeg m) ((P.ak.toList.map fun k => k.a + k.L) ++ P.gk.toList.map GK.l ++
    P.str.toList.map fun F => F.p + F.n)
  let sb := segTab (sfSeg b) (P.ak.toList.flatMap (fun k => k.ds.toList.map (· + k.L)) ++ P.str.toList.map SRunF.n)
  P.cls.foldl (fun s k => s + k.val fa m b ka kb fcv fw) 0 + P.kval fa m b fw ka kb mt sm sb B11 MH BH +
    rsum P.rest fa (twT b) fs fcv (fun c => fw (2 * c + 1) + KT.mX (fw (2 * c + 2))) fw m b.tail +
    P.rk.valW fa fs fw fcv (twT b)

/-- **The class evaluator of `Φ_Q`** (by the entries at a point not of 43 coordinates). -/
def PT.eval (P : PT) (pt : List FE2) : FE2 :=
  if pt.length = 43 then
    let a := pt.take 2
    let m := (pt.drop 2).take 20
    let b := pt.drop 22
    let at4 := ((List.range 4).map fun o => eqAtF a o).toArray
    let sm := mkSEqF m
    let st := mkSEqF b.tail
    let sb := mkSEqF b
    P.evalW m b (fun o => if h : o < at4.size then at4[o] else eqAtF a o) (fun x => sm.atI m x)
      (fun c => st.atI b.tail c) (fun y => sb.atI b y) sm.lo st.lo sb.lo sm.hi sb.hi
  else ((P.ents.map toIdx).map fun e => e.1 * eqAtF pt e.2).sum

/-! ## Correctness -/

theorem mX_xF (a : FE2) : KT.mX a = xF * a := KT.mX_eq a

theorem class_val (k : CTpl) (pt : List FE2) (hl : pt.length = 43) (hk : k.okB = true) (fa fcv fw : ℕ → FE2)
    (hfa : ∀ o, fa o = eqAtF (pt.take 2) o) (hfc : ∀ c, fcv c = eqAtF (pt.drop 22).tail c)
    (hfw : ∀ y, fw y = eqAtF (pt.drop 22) y) (ka kb : Array (Array FE2 × ℕ))
    (hka : ∀ j i, ktF ka ((pt.drop 2).take 20) j i = eqAtF (((pt.drop 2).take 20).take j) i)
    (hkb : ∀ j i, klF (kb.getD j (#[], 0)).1 (kb.getD j (#[], 0)).2 ((pt.drop 22).take j).tail i =
      eqAtF ((pt.drop 22).take j).tail i) :
    k.val fa ((pt.drop 2).take 20) (pt.drop 22) ka kb fcv fw =
      (k.ents.map (qv fa (eqAtF ((pt.drop 2).take 20)) (eqAtF (pt.drop 22)))).sum := by
  obtain rfl : fa = eqAtF (pt.take 2) := funext hfa
  obtain rfl : fcv = eqAtF (pt.drop 22).tail := funext hfc
  obtain rfl : fw = eqAtF (pt.drop 22) := funext hfw
  have hm : ((pt.drop 2).take 20).length = 20 := by simp [hl]
  have hb : (pt.drop 22).length = 21 := by simp [hl]
  have hk2 := hk
  simp only [CTpl.okB, Bool.and_eq_true, decide_eq_true_eq] at hk2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hbb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h1⟩ := hk2
  rw [class_eq _ _ _ k (by omega) (by omega) hk]
  have hbne : pt.drop 22 ≠ [] := by intro h; rw [h] at hb; simp at hb
  obtain ⟨b0, bt, hbe⟩ := List.exists_cons_of_ne_nil hbne
  have hbt : (pt.drop 22).take k.bb ≠ [] := by
    rw [hbe, show k.bb = (k.bb - 1) + 1 by omega, List.take_succ_cons]; simp
  have hT : twT ((pt.drop 22).take k.bb) = twT (pt.drop 22) := by
    rw [hbe, show k.bb = (k.bb - 1) + 1 by omega, List.take_succ_cons]; rfl
  have hylo : ∀ w, mulE (if w % 2 = 1 then (pt.drop 22).headD 0 else 1 + (pt.drop 22).headD 0)
      (eqAtF ((pt.drop 22).take k.bb).tail (w / 2)) = eqAtF ((pt.drop 22).take k.bb) w := by
    intro w
    rw [mulE_eq, hbe, show k.bb = (k.bb - 1) + 1 by omega, List.take_succ_cons, eqAtF_succ]
    simp
  have hal0 := twin_al ((pt.drop 22).take k.bb) hbt
  rw [hT] at hal0
  unfold CTpl.val
  simp only [hka, hkb, hylo, mX_xF]
  rw [clsCombF2_eq, clsCombF_eq]
  rw [rsum_eq _ _ _ _ _ _ hal0 (fun c => rfl) _ _ (fun x => rfl) (fun c => rfl),
    rsum_eq _ _ _ _ _ _ hal0 (fun c => rfl) _ _ (fun x => rfl) (fun c => rfl),
    rsum_eq _ _ _ _ _ _ (twin_al _ hbne) (fun c => rfl) _ _ (fun x => rfl) (fun c => rfl)]
  rfl

theorem evalW_eq (P : PT) (hok : P.okB = true) (pt : List FE2) (hl : pt.length = 43) (fa fs fcv fw : ℕ → FE2)
    (hfa : ∀ o, fa o = eqAtF (pt.take 2) o) (hfs : ∀ x, fs x = eqAtF ((pt.drop 2).take 20) x)
    (hfc : ∀ c, fcv c = eqAtF (pt.drop 22).tail c) (hfw : ∀ y, fw y = eqAtF (pt.drop 22) y)
    (K11 B12 B11 MH BH : Array FE2)
    (hK : K11 = kerF (((pt.drop 2).take 20).take 11)) (hB : B12 = kerF ((pt.drop 22).take 12).tail)
    (hB11 : B11 = kerF ((pt.drop 22).take 11)) (hMH : MH = kerF (((pt.drop 2).take 20).drop 11)) (hBH : BH = kerF ((pt.drop 22).drop 11)) :
    P.evalW ((pt.drop 2).take 20) (pt.drop 22) fa fs fcv fw K11 B12 B11 MH BH =
      (P.ents.map (qv (eqAtF (pt.take 2)) (eqAtF ((pt.drop 2).take 20)) (eqAtF (pt.drop 22)))).sum := by
  have hb : (pt.drop 22) ≠ [] := by intro h; have := congrArg List.length h; simp [hl] at this
  obtain rfl : fa = eqAtF (pt.take 2) := funext hfa
  obtain rfl : fs = eqAtF ((pt.drop 2).take 20) := funext hfs
  obtain rfl : fcv = eqAtF (pt.drop 22).tail := funext hfc
  obtain rfl : fw = eqAtF (pt.drop 22) := funext hfw
  simp only [PT.okB, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hokc, hokk⟩ := hok
  unfold PT.evalW PT.ents
  simp only
  rw [List.map_append, List.map_append, List.map_append, List.sum_append, List.sum_append, List.sum_append,
    sum_map_flatMap, ← Array.foldl_toList, foldl_add_eq, zero_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg List.sum (List.map_congr_left fun k hk => ?_)) ?_) ?_) ?_
  · exact class_val k pt hl (hokc k hk) _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _
      (ktFS2_eq _ _ _ hK) (kbTabS_ok _ _ _ hB)
  · exact kval_eq P hokk _ _ _ (by simp [hl]) (by simp [hl]) _ (fun _ => rfl) _ _ (ktFS2_eq _ _ _ hK)
      (kbTabS_ok _ _ _ hB) _ _ _ _ _ _ hB11 hMH hBH
  · exact rsum_eq _ _ _ _ _ _ (twin_al _ hb) (fun c => by rw [mX_xF]) _ _ (fun x => rfl) (fun c => rfl) _
  · exact P.rk.valW_eq _ _ _ _ _ (twin_al _ hb)

/-- **The evaluator is the sum over its entries.** -/
theorem eval_ents (P : PT) (hok : P.okB = true) (hb : P.ents.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) = true)
    (pt : List FE2) : P.eval pt = ((P.ents.map toIdx).map fun e => e.1 * eqAtF pt e.2).sum := by
  unfold PT.eval
  split
  · rename_i hl
    simp only
    refine (evalW_eq P hok pt hl _ _ _ _ ?_ ?_ ?_ ?_ _ _ _ _ _ rfl ?_ rfl rfl rfl).trans ?_
    · intro o; split <;> simp
    · intro x; rw [SEq.atI_eq, mkSEqF_eq, mkSEq_at]
    · intro c; rw [SEq.atI_eq, mkSEqF_eq, mkSEq_at]
    · intro y; rw [SEq.atI_eq, mkSEqF_eq, mkSEq_at]
    · show kerF ((pt.drop 22).tail.take 11) = kerF ((pt.drop 22).take 12).tail
      cases pt.drop 22 <;> simp
    · rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨ho, hx⟩ := hb q hq
      simp only [Function.comp_apply, toIdx, qv, eq3 pt hl _ _ _ ho hx]
  · rfl

/-! ## PHIV7: the fast evaluator -/

/-- PHIV7: `PT.kval` with the affine kinds by `AK.valK2`. -/
@[specialize] def PT.kval7 (P : PT) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 MH BH : Array FE2) : FE2 :=
  let MHp := kpair (m.drop 11) MH
  let BHp := kpair (b.drop 11) BH
  P.ak.foldl (fun s k => s + k.valK2 fa m b fw ka kb mt sm sb B11 MHp BHp) 0 +
    P.str.foldl (fun s F => s + F.valGS fa (sufT m sm MHp (F.p + F.n)) (sufL b sb F.n) (sufH b sb BHp F.n)
      (sufM F.n) m b) 0 +
    P.gk.foldl (fun s g => s + g.valW fa (ktG ka m g.l) (sufT m sm MHp g.l) (fun w => B11.getD w 0)
      (fun v => klG BHp v fun _ => eqAtF (b.drop 11) v)) 0 +
    P.bk.foldl (fun s k => s + k.valW fa m b) 0

theorem PT.kval7_eq (P : PT) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 MH BH : Array FE2) :
    P.kval7 fa m b fw ka kb mt sm sb B11 MH BH = P.kval fa m b fw ka kb mt sm sb B11 MH BH := by
  unfold PT.kval7 PT.kval
  simp only [AK.valK2_eq]

/-- PHIV7: `PT.evalW` with the twins: classes by `CTpl.val2`, kinds by `PT.kval7`, the rest's singles grouped
(`rsumK`). -/
@[specialize] def PT.evalW7 (P : PT) (m b : List FE2) (fa fs fcv fw : ℕ → FE2) (K11 B12 B11 MH BH : Array FE2) :
    FE2 :=
  let ka := kerTabS2 m (P.cls.toList.map CTpl.a ++ (P.ak.toList.filterMap fun k => if k.a ≤ 11 then some k.a else none)
    ++ P.gk.toList.map GK.l) K11
  let kb := kbTabS b (P.cls.toList.map CTpl.bb ++ P.ak.toList.flatMap fun k => k.ds.toList.filter (· ≤ 12)) B12
  let mt := segTab (midSeg b) (P.ak.toList.flatMap fun k => k.ds.toList.filter (12 < ·))
  let sm := segTab (sfSeg m) ((P.ak.toList.map fun k => k.a + k.L) ++ P.gk.toList.map GK.l ++
    P.str.toList.map fun F => F.p + F.n)
  let sb := segTab (sfSeg b) (P.ak.toList.flatMap (fun k => k.ds.toList.map (· + k.L)) ++ P.str.toList.map SRunF.n)
  P.cls.foldl (fun s k => s + k.val2 fa m b ka kb fcv fw (hwB b BH) (lwB B11)) 0 +
    P.kval7 fa m b fw ka kb mt sm sb B11 MH BH +
    rsumK P.rest fa (twT b) fs fcv (fun c => fw (2 * c + 1) + KT.mX (fw (2 * c + 2))) fw m b.tail (· / 2048) (hwB b BH)
      (lwB B11) +
    P.rk.valW fa fs fw fcv (twT b)

/-- `PT.evalW7` is `PT.evalW` when the word weights split on the kernels `B11`, `BH`. -/
theorem PT.evalW7_eq (P : PT) (m b : List FE2) (fa fs fcv fw : ℕ → FE2) (K11 B12 B11 MH BH : Array FE2)
    (h : ∀ y, fw y = hwB b BH (y / 2048) * lwB B11 y) :
    P.evalW7 m b fa fs fcv fw K11 B12 B11 MH BH = P.evalW m b fa fs fcv fw K11 B12 B11 MH BH := by
  unfold PT.evalW7 PT.evalW
  simp only [CTpl.val2_eq _ _ _ _ _ _ _ _ _ _ h, PT.kval7_eq, rsumK_eq _ _ _ _ _ _ _ _ _ _ _ _ h]

/-- **PHIV7: the fast class evaluator of `Φ_Q`** (`PT.eval` with the twins). -/
def PT.eval7 (P : PT) (pt : List FE2) : FE2 :=
  if pt.length = 43 then
    let a := pt.take 2
    let m := (pt.drop 2).take 20
    let b := pt.drop 22
    let at4 := ((List.range 4).map fun o => eqAtF a o).toArray
    let sm := mkSEqF m
    let st := mkSEqF b.tail
    let sb := mkSEqF b
    P.evalW7 m b (fun o => if h : o < at4.size then at4[o] else eqAtF a o) (fun x => sm.atI m x)
      (fun c => st.atI b.tail c) (fun y => sb.atI b y) sm.lo st.lo sb.lo sm.hi sb.hi
  else ((P.ents.map toIdx).map fun e => e.1 * eqAtF pt e.2).sum

/-- **`PT.eval7 = PT.eval`**, for every table and every point. -/
theorem PT.eval7_eq (P : PT) (pt : List FE2) : P.eval7 pt = P.eval pt := by
  unfold PT.eval7 PT.eval
  split
  · rename_i hl
    dsimp only
    refine PT.evalW7_eq _ _ _ _ _ _ _ _ _ _ _ _ fun y => ?_
    have hb : 11 ≤ (pt.drop 22).length := by simp [hl]
    have hat : (mkSEqF (pt.drop 22)).atI (pt.drop 22) y = eqAtF (pt.drop 22) y := by
      rw [SEq.atI_eq, mkSEqF_eq, mkSEq_at]
    rw [hat]
    exact eq_split11 _ hb _ _ rfl rfl y
  · rfl

/-! ## The start-up check -/

/-- Adjacent entries of equal index merged. -/
def comb : List (FE2 × ℕ) → List (FE2 × ℕ)
  | [] => []
  | (c, i) :: rest =>
    match comb rest with
    | (c', i') :: r => if i = i' then (c + c', i) :: r else (c, i) :: (c', i') :: r
    | [] => [(c, i)]

theorem comb_sum (f : ℕ → FE2) : ∀ l : List (FE2 × ℕ),
    ((comb l).map fun p => p.1 * f p.2).sum = (l.map fun p => p.1 * f p.2).sum
  | [] => rfl
  | (c, i) :: rest => by
    have ih := comb_sum f rest
    unfold comb
    split
    · rename_i c' i' r h
      rw [h] at ih
      split
      · rename_i he
        subst he
        simp only [List.map_cons, List.sum_cons] at ih ⊢
        rw [← ih]; ring
      · simp only [List.map_cons, List.sum_cons] at ih ⊢
        rw [← ih]
    · rename_i h
      rw [h] at ih
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ih ⊢
      rw [← ih]

theorem filter_sum (f : ℕ → FE2) : ∀ l : List (FE2 × ℕ),
    ((l.filter fun p => p.1 != 0).map fun p => p.1 * f p.2).sum = (l.map fun p => p.1 * f p.2).sum
  | [] => rfl
  | p :: l => by
    rw [List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons, filter_sum f l, List.map_cons, List.sum_cons]
    · rename_i h
      have h0 : p.1 = 0 := by simpa using h
      rw [filter_sum f l, List.map_cons, List.sum_cons, h0, zero_mul, zero_add]

/-- **The normal form of an entry list**: sorted by index, equal indices merged, zeros dropped. -/
def normL (l : List (FE2 × ℕ)) : List (FE2 × ℕ) :=
  (comb (l.mergeSort fun p q => decide (p.2 ≤ q.2))).filter fun p => p.1 != 0

theorem normL_sum (f : ℕ → FE2) (l : List (FE2 × ℕ)) :
    ((normL l).map fun p => p.1 * f p.2).sum = (l.map fun p => p.1 * f p.2).sum := by
  unfold normL
  rw [filter_sum, comb_sum]
  exact ((List.mergeSort_perm l _).map _).sum_eq

/-- **The start-up check**: the classes fit, every entry is on `Φ_Q`'s cube, and the expansion equals the
entries after merging. -/
def ptCheck (P : PT) (es : List EntT) : Bool :=
  P.okB && P.ents.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) &&
    decide (normL (P.ents.map toIdx) = normL (es.map keyE))

/-- **The class evaluator computes `Φ_Q`** once the start-up check passed. -/
theorem phiOk_pt {Q : Program} {lay : Lay} {P : PT} (h : ptCheck P (Lvm6.Ty.entsE Q lay) = true) :
    PhiOk P.eval Q lay := by
  intro pt
  simp only [ptCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, hb⟩, hn⟩ := h
  have hb' : P.ents.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) = true := hb
  rw [eval_ents P hok hb' pt, ← normL_sum (eqAtF pt), hn, normL_sum, Lvm6.Ty.PhiQFE, foldr_add_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [Function.comp_apply, keyE, eqWT_eq]

/-- **The typed phase with the class evaluator.** -/
theorem tw_typedPhase6_pt (sh : Lvm6.Shape) (i : Lvm6.Ty.TyInst6) (hlay : Lvm6.QD.TyLayOk i.Ti) {P : PT}
    (h : ptCheck P (Lvm6.Ty.entsE i.Ti.Q i.Ti.lay) = true) :
    TwinF (List.map FClaim.dec) (Lvm6.Ty.typedPhase6 sh i) (fTypedPhase6 sh i P.eval) :=
  tw_typedPhase6 sh i hlay (phiOk_pt h)

/-! ## The table of LAY's class table (a hint) -/

/-- A flat cover with `W` runs of a list of entries (`x`, `y` relative), the runs taken out first when `runs`. -/
def mkRCov (es : List EntT) (runs : Bool) : RCov := Id.run do
  if !runs then return ⟨FCov.ofCov (mkCov es), #[]⟩
  let key (o x y : ℕ) : ℕ × ℕ × ℕ := (o, x, y)
  let m : Std.HashMap (ℕ × ℕ × ℕ) FE2 := es.foldl (fun m e => m.insert (key e.o e.x e.y) e.c) {}
  let isW (x : ℕ) : Bool := m.get? (3, x, 2 * x) == some 1 && m.get? (3, x, 2 * x + 1) == some xF
  let ws := ((es.filterMap fun e => if e.o = 3 && e.y = 2 * e.x && isW e.x then some e.x else none).toArray.qsort
    (· < ·))
  let others := es.filter fun e => !(e.o = 3 && (e.y = 2 * e.x || e.y = 2 * e.x + 1) && isW e.x)
  let mut runs : Array (ℕ × ℕ) := #[]
  for x in ws do
    match runs.back? with
    | some (s, e) => if e = x then runs := runs.pop.push (s, x + 1) else if e < x + 1 then runs := runs.push (x, x + 1)
    | none => runs := runs.push (x, x + 1)
  return ⟨FCov.ofCov (mkCov others), runs⟩

/-- **The class evaluator's table of LAY's class table** (not proved: `ptCheck` decides). -/
def PT.ofCls (T : Lvm6.Phi.PhiCls) : PT :=
  let cls := T.cls.map fun k =>
    let part (d : ℕ) : List EntT := (k.tpl.filter (·.d = d)).map fun e => ⟨e.o, e.i, e.w, e.c⟩
    (⟨k.g.xb, k.g.a, k.g.yb, k.g.b, k.g.n, (if k.g.n ≤ 1 then 0 else Nat.log2 (k.g.n - 1) + 1), mkRCov (part 0) true, mkRCov (part 1) false,
      mkRCov (part 2) false⟩ : CTpl)
  ⟨cls.toArray, mkRCov T.rest (T.wb == 0), #[], #[], #[], #[], ⟨#[]⟩⟩

end Lvm6.V
