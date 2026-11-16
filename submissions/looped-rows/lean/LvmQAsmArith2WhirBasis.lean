-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 3: the claims as trie terms
-- and the batched basis `Σ_i s^i · onStack_i(x)` (`basisG`, `basisG_spec`); with `targetG`
-- (`LvmQAsmArith2WhirBasis0`) the two values `verifyStackedOpening` batches.
import LvmQAsmArith2WhirG

-- ===== merged from `LvmQAsmArith2WhirBasis0` (GOLF module merge: `LvmQAsmArith2WhirBasis0.lean` is now a stub importing `LvmQAsmArith2WhirBasis`) =====
section
-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 1: pointer-free gadget specs
-- (`Hs`), the binary trie over static selector keys (`trieG`), memoised `eq` chains (`chainG`), the
-- batched target (`targetG`), `F`'s `dot (powers s n)` as a running sum (`bsum`).

/-!
# Claim batching, part 1: trie, chains, target

* **`Hs c M m P`**: wherever the gadget `m` is placed, if its rows hold its output satisfies `P`
  (`hs_bind`, `hs_pure`, `hs_mono`, `hs_mulAdd`, `hs_lin`): the specs below need no pointer.
* **Terms** `TC = (scale cell, key, leaf cell)`, value `scale · Π_j f(key_j, x_{n−1−j}) · leaf`
  (`tval`, `kprod`), `f(0, y) = 1 + y`, `f(1, y) = y` (`fb`): a key fixes the top coordinates of the
  point bit by bit. **`trieG xb z n ts`**: `Σ_t tval t` by a binary trie over the keys from the top
  coordinate `n − 1` (coordinate `i` in the `E` cell `xb + i`): a node is
  `Σ_here scale·leaf + (1 + x) V₀ + x V₁` (two rows; one row with one child; none when empty).
  Rows: one per term, one per one-child node, two per two-child node. `trieG_spec`.
* **`chainG`**: `Π_{i<n} (1 + z_i + x_i)` for a cell list `z`, memoised by prefix (a hit costs
  nothing, a new prefix two rows; invariant `MemoOk`). `chainG_spec`.
* **`targetG`**: `Σ_i s^i v_i`, one `mulAdd` per claim. `targetG_spec`; `dot_powers_bsum`:
  `F`'s `dot (powers s |w|) w` is `bsum s 0 w`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Pointer-free specs -/

/-- Wherever `m` is placed, if its rows hold, its output satisfies `P`. -/
def Hs (c : Ctx) (M : Mem) {α : Type} (m : BM α) (P : α → Prop) : Prop :=
  ∀ p : Ptr, SegsHold c M p (m p).2 → P (m p).1

variable {c : Ctx} {M : Mem}

theorem hs_bind {α β : Type} {m : BM α} {f : α → BM β} {P : α → Prop} {Q : β → Prop}
    (hm : Hs c M m P) (hf : ∀ a, P a → Hs c M (f a) Q) : Hs c M (m >>= f) Q := by
  intro p h
  rw [hold_bind] at h
  exact hf _ (hm p h.1) _ h.2

theorem hs_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : Hs c M (pure a) P := fun _ _ => h

theorem hs_mono {α : Type} {m : BM α} {P Q : α → Prop} (h : Hs c M m P) (hPQ : ∀ a, P a → Q a) :
    Hs c M m Q := fun p hp => hPQ _ (h p hp)

theorem hs_mulAdd (τ : Ty) (a b d : Cell) :
    Hs c M (mulAdd τ a b d) (fun r => r.val M = a.val M * b.val M + d.val M) := fun _ h => mulAdd_spec h

theorem hs_lin (τ : Ty) (k k' : FK) (a b : Cell) :
    Hs c M (lin τ k k' a b) (fun r => r.val M = a.val M + FE.ofK k * b.val M + FE.ofK k') :=
  fun _ h => lin_spec h

/-! ## Terms and the trie -/

/-- A term: scale cell, key (top coordinate first), leaf cell. -/
structure TC where
  /-- The scale. -/
  sc : Cell
  /-- The fixed top coordinates' bits, the top one first. -/
  key : List Bool
  /-- The leaf (the weight over the coordinates below the key). -/
  lf : Cell

/-- The factor of a fixed coordinate: `y` for bit 1, `1 + y` for bit 0. -/
def fb (b : Bool) (y : FE) : FE := if b then y else 1 + y

/-- The product of a key's factors, the first bit at coordinate `n − 1`. -/
def kprod (X : Nat → FE) : Nat → List Bool → FE
  | _, [] => 1
  | 0, _ :: _ => 1
  | n + 1, b :: bs => fb b (X n) * kprod X n bs

/-- A term's value below coordinate `n`. -/
def tval (M : Mem) (X : Nat → FE) (n : Nat) (t : TC) : FE := t.sc.val M * kprod X n t.key * t.lf.val M

/-- The terms whose key ends here. -/
def here (ts : List TC) : List TC := ts.filter fun t => t.key.isEmpty

/-- The terms whose key continues with bit `b`, the bit removed. -/
def sub (b : Bool) (ts : List TC) : List TC := ts.filterMap fun t => match t.key with
  | b' :: r => if b' = b then some ⟨t.sc, r, t.lf⟩ else none
  | [] => none

/-- `w + Σ_t scale·leaf`, one row per term. -/
def hereG : Cell → List TC → BM Cell
  | w, [] => pure w
  | w, t :: ts => do
    let w' ← mulAdd .E t.sc t.lf w
    hereG w' ts

/-- A trie node: `(1 + x) V₀ + x V₁` from the children (`b₀`/`b₁`: the child is empty). -/
def node (xc z : Cell) : Bool → Bool → BM Cell → BM Cell → BM Cell
  | true, true, _, _ => pure z
  | false, true, m0, _ => do
    let v ← m0
    mulAdd .E xc v v
  | true, false, _, m1 => do
    let v ← m1
    mulAdd .E xc v z
  | false, false, m0, m1 => do
    let v0 ← m0
    let v1 ← m1
    let u ← add v0 v1
    mulAdd .E xc u v0

/-- **The trie** of the terms below coordinate `n` (coordinate `i` in the `E` cell `xb + i`). -/
def trieG (xb : Nat) (z : Cell) : Nat → List TC → BM Cell
  | 0, ts => hereG z ts
  | n + 1, ts => do
    let w ← node (ec (xb + n)) z (sub false ts).isEmpty (sub true ts).isEmpty
      (trieG xb z n (sub false ts)) (trieG xb z n (sub true ts))
    hereG w (here ts)

theorem hereG_spec : ∀ (ts : List TC) (w : Cell), Hs c M (hereG w ts)
    (fun r => r.val M = w.val M + (ts.map fun t => t.sc.val M * t.lf.val M).sum)
  | [], w => hs_pure (by simp)
  | t :: ts, w => by
    show Hs c M (mulAdd .E t.sc t.lf w >>= fun w' => hereG w' ts) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun w' hw' => hs_mono (hereG_spec ts w') fun r hr => ?_
    rw [hr, hw', List.map_cons, List.sum_cons]
    ring

theorem node_spec {xc z : Cell} (hz : z.val M = 0) {b0 b1 : Bool} {m0 m1 : BM Cell} {A0 A1 : FE}
    (h0 : Hs c M m0 (fun v => v.val M = A0)) (h1 : Hs c M m1 (fun v => v.val M = A1))
    (e0 : b0 = true → A0 = 0) (e1 : b1 = true → A1 = 0) :
    Hs c M (node xc z b0 b1 m0 m1) (fun w => w.val M = (1 + xc.val M) * A0 + xc.val M * A1) := by
  cases b0 <;> cases b1
  · refine hs_bind h0 fun v hv => hs_bind h1 fun v1 hv1 => hs_bind (hs_lin _ _ _ _ _) fun u hu =>
      hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hu, hv, hv1, ofK_one, ofK_zero]
    ring
  · refine hs_bind h0 fun v hv => hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hv, e1 rfl]
    ring
  · refine hs_bind h1 fun v hv => hs_mono (hs_mulAdd _ _ _ _) fun w hw => ?_
    rw [hw, hv, hz, e0 rfl]
    ring
  · exact hs_pure (by rw [hz, e0 rfl, e1 rfl]; ring)

theorem here_nil (sc lf : Cell) (ts : List TC) : here (⟨sc, [], lf⟩ :: ts) = ⟨sc, [], lf⟩ :: here ts := rfl
theorem here_cons (sc lf : Cell) (b : Bool) (r : List Bool) (ts : List TC) :
    here (⟨sc, b :: r, lf⟩ :: ts) = here ts := rfl
theorem sub_nil (b : Bool) (sc lf : Cell) (ts : List TC) : sub b (⟨sc, [], lf⟩ :: ts) = sub b ts := rfl
theorem sub_same (b : Bool) (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub b (⟨sc, b :: r, lf⟩ :: ts) = ⟨sc, r, lf⟩ :: sub b ts := by cases b <;> rfl
theorem sub_ft (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub true (⟨sc, false :: r, lf⟩ :: ts) = sub true ts := rfl
theorem sub_tf (sc lf : Cell) (r : List Bool) (ts : List TC) :
    sub false (⟨sc, true :: r, lf⟩ :: ts) = sub false ts := rfl

theorem sum_split (X : Nat → FE) (n : Nat) : ∀ ts : List TC,
    (ts.map (tval M X (n + 1))).sum = ((here ts).map fun t => t.sc.val M * t.lf.val M).sum +
      (1 + X n) * ((sub false ts).map (tval M X n)).sum + X n * ((sub true ts).map (tval M X n)).sum
  | [] => by simp [here, sub]
  | ⟨sc, key, lf⟩ :: ts => by
    have ih := sum_split X n ts
    rcases key with _ | ⟨b, r⟩
    · rw [here_nil, sub_nil, sub_nil, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
      simp only [tval, kprod]
      ring
    · cases b
      · rw [here_cons, sub_same, sub_ft, List.map_cons, List.map_cons,
          List.sum_cons, List.sum_cons, ih]
        simp only [tval, kprod, fb, Bool.false_eq_true, if_false]
        ring
      · rw [here_cons, sub_same, sub_tf, List.map_cons, List.map_cons,
          List.sum_cons, List.sum_cons, ih]
        simp only [tval, kprod, fb, if_true]
        ring

theorem sum_nil_of_isEmpty {ts : List TC} {g : TC → FE} (h : ts.isEmpty = true) : (ts.map g).sum = 0 := by
  rw [List.isEmpty_iff] at h; subst h; rfl

/-- **The trie**: its cell is `Σ_t tval t` (coordinate `i` in the `E` cell `xb + i`). -/
theorem trieG_spec {xb : Nat} {z : Cell} (hz : z.val M = 0) : ∀ (n : Nat) (ts : List TC),
    Hs c M (trieG xb z n ts) (fun r => r.val M = (ts.map (tval M (fun i => M.e (xb + i)) n)).sum)
  | 0, ts => by
    refine hs_mono (hereG_spec ts z) fun r hr => ?_
    rw [hr, hz, zero_add]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    rcases t with ⟨sc, key, lf⟩
    rcases key with _ | ⟨b, r⟩ <;> simp only [tval, kprod, mul_one]
  | n + 1, ts => by
    show Hs c M (node (ec (xb + n)) z (sub false ts).isEmpty (sub true ts).isEmpty
      (trieG xb z n (sub false ts)) (trieG xb z n (sub true ts)) >>= fun w => hereG w (here ts)) _
    refine hs_bind (node_spec hz (trieG_spec hz n _) (trieG_spec hz n _) sum_nil_of_isEmpty sum_nil_of_isEmpty)
      fun w hw => hs_mono (hereG_spec _ w) fun r hr => ?_
    rw [hr, hw, sum_split]
    simp only [Cell.val_E]
    ring

/-! ## Memoised `eq` chains -/

/-- The memo: prefixes and their chain cells. -/
abbrev Memo := List (List Cell × Cell)

/-- `Π_{i<n} (1 + z_i + x_i)`. -/
def cv (M : Mem) (X : Nat → FE) (l : List Cell) (n : Nat) : FE :=
  ∏ i ∈ Finset.range n, (1 + (l.getD i default).val M + X i)

/-- Every memo entry holds its prefix's chain. -/
def MemoOk (M : Mem) (X : Nat → FE) (memo : Memo) : Prop := ∀ e ∈ memo, e.2.val M = cv M X e.1 e.1.length

/-- **The chain of the first `n` cells of `zl`**, from the memo or extended from the chain of
the first `n − 1` (`o` holds `1`, `z` holds `0`). -/
def chainG (xb : Nat) (z o : Cell) (zl : List Cell) : Nat → Memo → BM (Memo × Cell)
  | 0, memo => pure (memo, o)
  | n + 1, memo =>
    match memo.find? (fun e => e.1 == zl.take (n + 1)) with
    | some e => pure (memo, e.2)
    | none => do
      let r ← chainG xb z o zl n memo
      let f ← lin .E 1 1 (zl.getD n default) (ec (xb + n))
      let c' ← mulAdd .E r.2 f z
      pure ((zl.take (n + 1), c') :: r.1, c')

theorem cv_take (X : Nat → FE) (l : List Cell) {m n : Nat} (h : n ≤ m) :
    cv M X (l.take m) n = cv M X l n := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) h
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi']

theorem chainG_spec {xb : Nat} {z o : Cell} {zl : List Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (n : Nat) (memo : Memo), n ≤ zl.length → MemoOk M (fun i => M.e (xb + i)) memo →
      Hs c M (chainG xb z o zl n memo)
        (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧ r.2.val M = cv M (fun i => M.e (xb + i)) zl n)
  | 0, memo, _, hm => hs_pure ⟨hm, by simp [cv, ho]⟩
  | n + 1, memo, hn, hm => by
    have hlen : (zl.take (n + 1)).length = n + 1 := by simp; omega
    rw [chainG]
    split
    · next e he =>
      refine hs_pure ⟨hm, ?_⟩
      have he1 : e.1 = zl.take (n + 1) := by simpa using List.find?_some he
      rw [hm e (List.mem_of_find?_eq_some he), he1, hlen, cv_take _ _ le_rfl]
    · refine hs_bind (chainG_spec hz ho n memo (by omega) hm) fun r ⟨hm', hv⟩ =>
        hs_bind (hs_lin _ _ _ _ _) fun f hf => hs_bind (hs_mulAdd _ _ _ _) fun c' hc' => hs_pure ⟨?_, ?_⟩
      · have hval : c'.val M = cv M (fun i => M.e (xb + i)) zl (n + 1) := by
          rw [hc', hf, hv, hz, cv, cv, Finset.prod_range_succ, ofK_one]
          simp only [Cell.val_E]
          ring
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rw [hlen, cv_take _ _ le_rfl, hval]
        · exact hm' e he
      · rw [hc', hf, hv, hz, cv, cv, Finset.prod_range_succ, ofK_one]
        simp only [Cell.val_E]
        ring

/-! ## The batched target -/

/-- `Σ_j s^(i+j) w_j`. -/
def bsum (s : FE) : Nat → List FE → FE
  | _, [] => 0
  | i, w :: ws => s ^ i * w + bsum s (i + 1) ws

theorem zip_powersFrom (s : FE) : ∀ (ws : List FE) (i : Nat) (a : FE),
    (List.zipWith (· * ·) (powersFrom (s ^ i) s ws.length) ws).foldl (· + ·) a = a + bsum s i ws
  | [], _, a => by simp [bsum, powersFrom]
  | w :: ws, i, a => by
    simp only [List.length_cons, powersFrom, List.zipWith_cons_cons, List.foldl_cons, bsum]
    rw [← pow_succ, zip_powersFrom s ws (i + 1)]
    ring

/-- **`F`'s batched sum**: `dot (powers s |w|) w = Σ_j s^j w_j`. -/
theorem dot_powers_bsum (s : FE) (ws : List FE) : Lvm.dot (powers s ws.length) ws = bsum s 0 ws := by
  have := zip_powersFrom s ws 0 0
  rw [pow_zero, zero_add] at this
  exact this

/-- The claim's value is its value cell's. -/
theorem cval_value (cc : CClaim) : (cc.val M).2.value = cc.value.val M := by
  rcases cc with ⟨com, cw, v⟩
  cases cw <;> rfl

/-- `acc + Σ_j s^(i+j) v_j` over the claims' value cells (`sp + i + j` holds `s^(i+j)`). -/
def targetGo (sp : Nat) : Nat → List CClaim → Cell → BM Cell
  | _, [], acc => pure acc
  | i, cc :: cl, acc => do
    let a ← mulAdd .E (ec (sp + i)) cc.value acc
    targetGo sp (i + 1) cl a

/-- `Σ_i s^i v_i` over the claims' value cells (`sp + i` holds `s^i`). -/
def targetG (cl : List CClaim) (sp : Nat) (z : Cell) : BM Cell := targetGo sp 0 cl z

theorem targetGo_spec {sp N : Nat} {s : FE} (hs : ∀ i < N, M.e (sp + i) = s ^ i) :
    ∀ (cl : List CClaim) (i : Nat) (acc : Cell), i + cl.length ≤ N →
      Hs c M (targetGo sp i cl acc)
        (fun r => r.val M = acc.val M + bsum s i (cl.map fun cc => cc.value.val M))
  | [], _, acc, _ => hs_pure (by simp [bsum])
  | cc :: cl, i, acc, hN => by
    simp only [List.length_cons] at hN
    show Hs c M (mulAdd .E (ec (sp + i)) cc.value acc >>= fun a => targetGo sp (i + 1) cl a) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun a ha =>
      hs_mono (targetGo_spec hs cl (i + 1) a (by omega)) fun r hr => ?_
    rw [hr, ha, List.map_cons, bsum, Cell.val_E, hs i (by omega)]
    ring

theorem targetG_spec {cl : List CClaim} {sp : Nat} {z : Cell} {p : Ptr} (h : SegsHold c M p (targetG cl sp z p).2)
    (hz : z.val M = 0) (s : FE) (hs : ∀ i < cl.length, M.e (sp + i) = s ^ i) :
    (targetG cl sp z p).1.val M = Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.value) := by
  have e := targetGo_spec (c := c) hs cl 0 z (by omega) p h
  rw [show (targetG cl sp z p).1 = (targetGo sp 0 cl z p).1 from rfl, e, hz, zero_add]
  have hl : cl.length = (cl.map fun cc => (cc.val M).2.value).length := by simp
  rw [hl, dot_powers_bsum]
  exact congrArg (bsum s 0) (List.map_congr_left fun cc _ => (cval_value cc).symm)

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2WhirBasis0` =====

-- ===== merged from `LvmQAsmArith2WhirBasis1` (GOLF module merge: `LvmQAsmArith2WhirBasis1.lean` is now a stub importing `LvmQAsmArith2WhirBasis`) =====
section
-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 2: the ring-switching leaf
-- `ringWeight pt x cs` with the coefficients given as cells (QA2's `ringWeightG` with the 64
-- coefficients copied instead of computed from the challenges; its proof adapted from
-- `LvmQRingWeight.ringWeight_eq`).

/-!
# Claim batching, part 2: the ring leaf

`ringLeaf vc pt cs xb z`: copies of the point cells `pt` (contiguous), QA2's factor tables
`fChunks` (`66·vc` rows) over the point and the coordinates `x_n` in the `E` cells `xb + n`
(`n < vc`, chunks `binDec 64 vc 0`: the binary digits of `vc`), copies of the 64 coefficient cells,
QA2's products `pChunks` (`64·vc` rows), the sum of the 64 products (65 rows).
`ringLeaf_spec`: the cell is `F`'s `ringWeight (vs M pt) ys (vs M cs)` for `ys = x.take vc`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing

variable {c : Ctx} {M : Mem}

/-- Copies of the cells at consecutive `E` cells from the pointer. -/
def copyN : List Cell → BM Unit
  | [] => pure ()
  | a :: cs => do
    let _ ← lin .E 0 0 a a
    copyN cs

theorem linE_adv (k k' : FK) (a b : Cell) (p : Ptr) : p.adv (lin .E k k' a b p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem copyN_adv : ∀ (cs : List Cell) (p : Ptr), p.adv (copyN cs p).2 = ⟨p.k, p.e + cs.length⟩
  | [], p => by simp [copyN, pure_apply]
  | a :: cs, p => by
    simp only [copyN]
    rw [bind_adv_eq rfl (linE_adv _ _ _ _ _), copyN_adv cs, List.length_cons]
    simp only [Ptr.mk.injEq, true_and]
    omega

theorem copyN_spec : ∀ (cs : List Cell) (p : Ptr), SegsHold c M p (copyN cs p).2 →
    ∀ k < cs.length, M.e (p.e + k) = (cs.getD k default).val M
  | [], _, _, k, hk => by simp at hk
  | a :: cs, p, h, k, hk => by
    simp only [copyN] at h
    rw [hold_bind_eq rfl (linE_adv _ _ _ _ _)] at h
    obtain ⟨h1, h2⟩ := h
    rcases k with _ | k
    · have e := lin_spec h1
      simp only [lin, rowRes, Ptr.at, Cell.val_E, ofK_zero, zero_mul, add_zero] at e
      simpa using e
    · have e := copyN_spec cs ⟨p.k, p.e + 1⟩ h2 k (by simpa using hk)
      simp only at e
      rw [show p.e + (k + 1) = p.e + 1 + k by ring, e]
      simp

/-- The binary digits of `n` from weight `2^k` (at most `fuel` of them), as exponents. -/
def binDec : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, n, k => if n = 0 then [] else (if n % 2 = 1 then [k] else []) ++ binDec f (n / 2) (k + 1)

/-- QA2's `ringWeightG` with the 64 coefficients copied from the cells `cs`. -/
def ringWeightC (bs : List Nat) (cs : List Cell) (r0 rp0 z : Nat) : BM Nat := do
  let Fs ← fChunks r0 rp0 0 bs
  copyN cs
  pChunks z bs Fs
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] 1 0 (eA (p.e - 64) [1]) (eA q.n [1])
  pure (q.n + 64)

/-- **The ring leaf**: `ringWeight pt x cs` over the first `vc` coordinates `x_n = M.e (xb + n)`. -/
def ringLeaf (vc : Nat) (pt cs : List Cell) (xb z : Nat) : BM Cell := do
  let p ← getPtr
  copyN pt
  let w ← ringWeightC (binDec 64 vc 0) cs p.e xb z
  pure (ec w)

theorem getD_map_val (l : List Cell) {n : Nat} (hn : n < l.length) :
    (vs M l).getD n 0 = (l.getD n default).val M := by
  simp [vs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem ringWeightC_spec {bs : List Nat} {cs : List Cell} {r0 rp0 z : Nat} {R R' : Nat → FE}
    (hcs : cs.length = 64) (hz : M.e z = 0)
    (hrv : ∀ n < sz bs, M.e (r0 + n) = R n) (hrpv : ∀ n < sz bs, M.e (rp0 + n) = R' n)
    {p : Ptr} (h : SegsHold c M p (ringWeightC bs cs r0 rp0 z p).2) :
    M.e (ringWeightC bs cs r0 rp0 z p).1 = ∑ i ∈ Finset.range 64,
      (cs.getD i default).val M * ∏ n ∈ Finset.range (sz bs), wf (R n) (R' n) i := by
  have hout : (ringWeightC bs cs r0 rp0 z p).1 = p.e + 130 * sz bs + 128 := by
    simp only [ringWeightC]
    rw [bind_fst_eq rfl (fChunks_adv _ _ _ _ _), bind_fst_eq rfl (copyN_adv _ _),
      bind_fst_eq rfl (pChunks_adv _ _ _ _), bind_fst_eq (getPtr_out _) (getPtr_adv _),
      bind_fst_eq (copy_out _ _) (copyE_adv _ _), bind_fst_eq rfl (linL_adv _ _ _ _ _ _), pure_apply]
    simp only [ec, Ptr.at, hcs]
    ring
  rw [hout]
  simp only [ringWeightC] at h
  rw [hold_bind_eq rfl (fChunks_adv _ _ _ _ _)] at h
  obtain ⟨hf, h⟩ := h
  rw [hold_bind_eq rfl (copyN_adv _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl (pChunks_adv _ _ _ _)] at h
  obtain ⟨hp, h⟩ := h
  rw [hcs] at hp
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq (copy_out _ _) (copyE_adv _ _)] at h
  obtain ⟨hq, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv' [6] 64 rfl _ _ _ _ _)] at h
  obtain ⟨hH, -⟩ := h
  have hF := fChunks_spec (R := R) (R' := R') bs 0 p (by simpa using hrv) (by simpa using hrpv) hf
  have hC := copyN_spec cs _ hc
  simp only [hcs] at hC
  have hP := pChunks_spec hz bs _ 0 ⟨p.k, p.e + 66 * sz bs + 64⟩
    (fun k => (cs.getD k default).val M) (by show 64 ≤ p.e + 66 * sz bs + 64; (clear * -; omega))
    (fun k hk => by
      rw [← hC k hk]
      show M.e (p.e + 66 * sz bs + 64 - 64 + k) = M.e (p.e + 66 * sz bs + k)
      rw [show p.e + 66 * sz bs + 64 - 64 + k = p.e + 66 * sz bs + k by (clear * -; omega)]) hF hp
  simp only [Nat.zero_add] at hP
  have h0 := (copyE_spec hq).2
  simp only [ec, Ptr.at, hcs] at h0 hH
  have hacc : ∀ k < 64, M.e (p.e + 66 * sz bs + 64 + 64 * sz bs + 1 + k) =
      ∑ j ∈ Finset.range (k + 1), (cs.getD j default).val M * ∏ n ∈ Finset.range (sz bs), wf (R n) (R' n) j := by
    intro k hk
    induction k with
    | zero =>
      have e := linL_spec hH (jf := 0) (by simp)
      simp only [Mem.rd, Addr.at, unflat_one (show 0 < 2 ^ 6 by norm_num), Loop.dot, Nat.add_zero,
        Nat.mul_zero, h0, hz, mul_zero, ofK_zero, ofK_one, one_mul, add_zero] at e
      rw [e, zero_add, Finset.sum_range_one]
      exact hP 0 hk
    | succ k ih =>
      have e := linL_spec hH (jf := k + 1) (by simpa using hk)
      simp only [Mem.rd, Addr.at, unflat_one (show k + 1 < 2 ^ 6 by simpa using hk), Loop.dot,
        Nat.add_zero, ofK_zero, ofK_one, one_mul, Nat.one_mul, add_zero] at e
      rw [e, Finset.sum_range_succ, ← ih (by (clear * - hk; omega)), ← hP (k + 1) hk, add_comm]
      congr 2
      (clear * -; omega)
  rw [show p.e + 130 * sz bs + 128 = p.e + 66 * sz bs + 64 + 64 * sz bs + 1 + 63 by ring,
    hacc 63 (by norm_num)]

/-- **The ring leaf**: `F`'s `ringWeight (vs M pt) ys (vs M cs)` for `ys` the first `vc`
coordinates (`ys_n = M.e (xb + n)`). -/
theorem ringLeaf_spec {vc xb z : Nat} {pt cs : List Cell} (hz : M.e z = 0) (hpt : pt.length = vc)
    (hcs : cs.length = 64) (hbs : sz (binDec 64 vc 0) = vc) (ys : List FE) (hys : ys.length = vc)
    (hy : ∀ n < vc, ys.getD n 0 = M.e (xb + n)) :
    Hs c M (ringLeaf vc pt cs xb z) (fun r => r.val M = ringWeight (vs M pt) ys (vs M cs)) := by
  intro p h
  simp only [ringLeaf] at h ⊢
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (copyN_adv _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl rfl] at h
  obtain ⟨hw, -⟩ := h
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _), bind_fst_eq rfl (copyN_adv _ _), bind_apply]
  simp only [pure_apply, Cell.val_E]
  have hC := copyN_spec pt _ hc
  rw [ringWeightC_spec (R := fun n => (vs M pt).getD n 0) (R' := fun n => ys.getD n 0) hcs hz
    (fun n hn => by rw [hC n (by (clear * - hpt hbs hys hn; omega)), getD_map_val pt (by (clear * - hpt hbs hys hn; omega))])
    (fun n hn => (hy n (by (clear * - hbs hys hn; omega))).symm) hw]
  have hl : (vs M pt).length = ys.length := by simp [vs, hpt, hys]
  rw [ringWeight_sum _ _ _ hl, hbs]
  have hl2 : (vs M cs).length = 64 := by simp [vs, hcs]
  have hl3 : (vs M pt).length = vc := by simp [vs, hpt]
  rw [hl2, hl3]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [getD_map_val cs (by rw [hcs]; exact Finset.mem_range.mp hi)]

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2WhirBasis1` =====

/-!
# Claim batching, part 3: the basis

Every claim becomes trie terms (`TC`, `LvmQAsmArith2WhirBasis0`) of value
`scale · Π_{i ∈ [k, ν)} f(bit_i, x_i) · leaf`:

* a point claim `(blk, z)`: one term, scale `s^i`; the bits are `eqAbove`'s selector bits on
  `[vc, ν)` and, below `vc`, the maximal suffix of `z` made of the constant cells `z` (bit 0) and
  `o` (bit 1) (`ncPre`, `bitP`); the leaf is the memoised chain `Π_{i<k} (1 + z_i + x_i)`
  (`chainG`: table claims share their point, so their chains are memo hits);
* a ring claim `(blk, pt, cs)`: one term, the selector bits on `[vc, ν)`, the leaf
  `ringWeight pt (x.take vc) cs` (`ringLeaf`);
* a sum claim `(nu, parts)`: one term per part, scale `s^i · c_j` (one row), bits 0 on `[nu, ν)`
  then the part's as for a point claim.

`partW_eq` is the algebra (`eqAbove`, `eqEval` as products of the factors `f(bit, x_i)`); the
terms' sum is `F`'s `dot (powers s n) (claims.map (·.onStack.1 x))` (`claimTerms_spec`,
`basisG_spec`). **Rows** (`E·E` `mulAdd` unless noted): `targetG` 1 per claim; `basisG`: per term
1 (leaf) + 1 per sum part (scale); per new chain prefix 2 (`E lin` + `mulAdd`); per one-child trie
node 1, per two-child node 2 (`E lin` + `mulAdd`); per ring claim `vc` + 64 copies (`E lin`),
`130·vc + 1` loop rows + 65 (QA2's `fChunks`/`pChunks`, 64-sum).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing

variable {c : Ctx} {M : Mem}

/-! ## Keys -/

/-- The length of `l` without its maximal suffix of constant cells (`z` or `o`). -/
def ncPre (z o : Cell) : List Cell → Nat
  | [] => 0
  | a :: l => if ncPre z o l = 0 ∧ (a = z ∨ a = o) then 0 else ncPre z o l + 1

theorem ncPre_le (z o : Cell) : ∀ l : List Cell, ncPre z o l ≤ l.length
  | [] => le_rfl
  | a :: l => by
    have := ncPre_le z o l
    simp only [ncPre, List.length_cons]
    split_ifs <;> omega

theorem ncPre_const (z o : Cell) : ∀ (l : List Cell) (i : Nat), ncPre z o l ≤ i → i < l.length →
    l.getD i default = z ∨ l.getD i default = o
  | [], _, _, hi => by simp at hi
  | a :: l, i, hk, hi => by
    simp only [ncPre] at hk
    split_ifs at hk with h
    · rcases i with _ | i
      · simpa using h.2
      · simpa using ncPre_const z o l i (by (clear * - h; omega)) (by simpa using hi)
    · rcases i with _ | i
      · (clear * - hk; omega)
      · simpa using ncPre_const z o l i (by (clear * - hk; omega)) (by simpa using hi)

/-- Bit `i` of the selector above a block (`eqAbove`'s `selectorPoint`). -/
def selbit (blk : Placement) (i : Nat) : Bool :=
  (blk.index >>> blk.variableCount >>> (i - blk.variableCount)) % 2 == 1

/-- The bit of coordinate `i` of a part of a claim on `nu` variables: 0 above `nu`, the selector
on `[vc, nu)`, the constant cell below. -/
def bitP (z o : Cell) (nu : Nat) (blk : Placement) (zl : List Cell) (i : Nat) : Bool :=
  if nu ≤ i then false else if blk.variableCount ≤ i then selbit blk i else zl.getD i default == o

/-- The key of the coordinates `[k, n)`, the top one first. -/
def keyOf (bit : Nat → Bool) : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, k => if n < k then [] else bit n :: keyOf bit n k

theorem kprod_keyOf (X : Nat → FE) (bit : Nat → Bool) (k : Nat) :
    ∀ n, kprod X n (keyOf bit n k) = ∏ i ∈ Finset.Ico k n, fb (bit i) (X i)
  | 0 => by simp [keyOf, kprod]
  | n + 1 => by
    simp only [keyOf]
    split_ifs with h
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]; rfl
    · rw [kprod, kprod_keyOf X bit k n, Finset.prod_Ico_succ_top (by omega)]
      ring

/-! ## The algebra -/

theorem eOfNat_zero : eOfNat 0 = 0 := rfl
theorem eOfNat_one : eOfNat 1 = 1 := rfl

theorem eOfNat_bit (b : Nat) (y : FE) : 1 + eOfNat (b % 2) + y = fb (b % 2 == 1) y := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> rw [h]
  · simp [fb, eOfNat_zero]
  · simp only [eOfNat_one, fb, beq_self_eq_true, if_true]
    rw [CharTwo.add_self_eq_zero, zero_add]

theorem getD_take' {α : Type} (l : List α) (d : α) {i m : Nat} (hi : i < m) :
    (l.take m).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

/-- **`eqAbove` as a product** of the factors `f(bit_i, y_i)` over `[vc, |ys|)`. -/
theorem eqAbove_prod (blk : Placement) (ys : List FE) (Y : Nat → FE) (hv : blk.variableCount ≤ ys.length)
    (hy : ∀ i < ys.length, ys.getD i 0 = Y i) :
    blk.eqAbove ys = ∏ i ∈ Finset.Ico blk.variableCount ys.length, fb (selbit blk i) (Y i) := by
  rw [Placement.eqAbove, eqEval_prod _ _ (by simp [selectorPoint]), Finset.prod_Ico_eq_prod_range]
  simp only [selectorPoint, List.length_map, List.length_range]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj', Option.map_some,
    Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    hy _ (by (clear * - hv hj'; omega)), eOfNat_bit, selbit, Nat.add_sub_cancel_left]

/-- The point `x` as a list. -/
def xsOf (M : Mem) (ν xb : Nat) : List FE := (List.range ν).map fun i => M.e (xb + i)

theorem xs_length (ν xb : Nat) : (xsOf M ν xb).length = ν := by simp [xsOf]

theorem xs_getD {ν xb i : Nat} (hi : i < ν) : (xsOf M ν xb).getD i 0 = M.e (xb + i) := by
  simp [xsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The selector-and-point part of a part's weight on `nu` variables. -/
def partW (M : Mem) (ν xb nu : Nat) (blk : Placement) (zl : List Cell) : FE :=
  blk.eqAbove ((xsOf M ν xb).take nu) * eqEval (vs M zl) (((xsOf M ν xb).take nu).take blk.variableCount)

/-- The zero selector bits above `nu`. -/
def e0f (M : Mem) (ν xb nu : Nat) : FE := ∏ i ∈ Finset.Ico nu ν, (1 + M.e (xb + i))

theorem bitP_hi {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : nu ≤ i) :
    bitP z o nu blk zl i = false := by simp [bitP, h]

theorem bitP_mid {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : ¬ nu ≤ i)
    (h' : blk.variableCount ≤ i) : bitP z o nu blk zl i = selbit blk i := by simp [bitP, h, h']

theorem bitP_lo {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : ¬ nu ≤ i)
    (h' : ¬ blk.variableCount ≤ i) : bitP z o nu blk zl i = (zl.getD i default == o) := by
  simp [bitP, h, h']

/-- **A part's weight as a product**: the key's factors on `[k, ν)` times the chain below `k`. -/
theorem partW_eq {ν xb nu : Nat} {z o : Cell} {blk : Placement} {zl : List Cell}
    (hz : z.val M = 0) (ho : o.val M = 1)
    (hzl : zl.length = blk.variableCount) (hvc : blk.variableCount ≤ nu) (hnu : nu ≤ ν) :
    (∏ i ∈ Finset.Ico (ncPre z o zl) ν, fb (bitP z o nu blk zl i) (M.e (xb + i))) *
        cv M (fun i => M.e (xb + i)) zl (ncPre z o zl) = e0f M ν xb nu * partW M ν xb nu blk zl := by
  have hk : ncPre z o zl ≤ blk.variableCount := hzl ▸ ncPre_le z o zl
  have hys : ((xsOf M ν xb).take nu).length = nu := by rw [List.length_take, xs_length]; (clear * - hnu; omega)
  have e1 : ∏ i ∈ Finset.Ico nu ν, fb (bitP z o nu blk zl i) (M.e (xb + i)) = e0f M ν xb nu :=
    Finset.prod_congr rfl fun i hi => by
      rw [bitP_hi (Finset.mem_Ico.mp hi).1]; rfl
  have e2 : ∏ i ∈ Finset.Ico blk.variableCount nu, fb (bitP z o nu blk zl i) (M.e (xb + i)) =
      blk.eqAbove ((xsOf M ν xb).take nu) := by
    rw [eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [hys]; exact hvc) (fun i hi => by
      rw [hys] at hi; rw [getD_take' _ _ hi, xs_getD (by (clear * - hnu hys hi; omega))]), hys]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    rw [bitP_mid (by (clear * - hys h2; omega)) h1]
  have hZ : ∀ i < blk.variableCount, (vs M zl).getD i 0 = (zl.getD i default).val M := fun i hi =>
    getD_map_val zl (by (clear * - hzl hi; omega))
  have e3 : eqEval (vs M zl) (((xsOf M ν xb).take nu).take blk.variableCount) =
      cv M (fun i => M.e (xb + i)) zl (ncPre z o zl) *
        ∏ i ∈ Finset.Ico (ncPre z o zl) blk.variableCount, fb (bitP z o nu blk zl i) (M.e (xb + i)) := by
    rw [eqEval_prod _ _ (by simp [vs, xs_length, hzl]; (clear * - hvc hnu hys; omega))]
    have hl : (vs M zl).length = blk.variableCount := by simp [vs, hzl]
    rw [hl, cv, ← Finset.prod_range_mul_prod_Ico _ hk]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hZ i (by (clear * - hk hl hi'; omega)), getD_take' _ _ (by (clear * - hk hl hi'; omega)), getD_take' _ _ (by (clear * - hvc hk hys hl hi'; omega)), xs_getD (by (clear * - hvc hnu hk hys hl hi'; omega))]
    · refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
      rw [hZ i h2, getD_take' _ _ h2, getD_take' _ _ (by (clear * - hvc hys hl h2; omega)), xs_getD (by (clear * - hvc hnu hys hl h2; omega)),
        bitP_lo (by (clear * - hvc hys hl h2; omega)) (by (clear * - hl h2; omega))]
      rcases ncPre_const z o zl i h1 (by (clear * - hzl hl h2; omega)) with hc | hc
      · by_cases ho' : zl.getD i default = o
        · rw [ho', ho, beq_self_eq_true, fb, if_pos rfl, CharTwo.add_self_eq_zero, zero_add]
        · have hb : (zl.getD i default == o) = false := by simpa using ho'
          rw [hb, hc, hz, fb, if_neg (by simp), add_zero]
      · rw [hc, ho, beq_self_eq_true, fb, if_pos rfl, CharTwo.add_self_eq_zero, zero_add]
  rw [partW, e3, ← e2, ← e1, ← Finset.prod_Ico_consecutive _ hk (le_trans hvc hnu),
    ← Finset.prod_Ico_consecutive _ hvc hnu]
  ring

/-! ## Terms of the claims -/

/-- The term of a part (a point claim, or a part of a sum claim on `nu` variables). -/
def partTerm (ν xb : Nat) (z o sc : Cell) (nu : Nat) (blk : Placement) (zl : List Cell) (memo : Memo) :
    BM (Memo × TC) := do
  let r ← chainG xb z o zl (ncPre z o zl) memo
  pure (r.1, ⟨sc, keyOf (bitP z o nu blk zl) ν (ncPre z o zl), r.2⟩)

/-- The term of a ring claim. -/
def ringTerm (ν xb : Nat) (z sc : Cell) (blk : Placement) (pt cs : List Cell) : BM TC := do
  let lf ← ringLeaf blk.variableCount pt cs xb z.n
  pure ⟨sc, keyOf (selbit blk) ν blk.variableCount, lf⟩

/-- The terms of a sum claim's parts (scale `sc · c_j`). -/
def partsTerms (ν xb : Nat) (z o sc : Cell) (nu : Nat) :
    List (Cell × Placement × List Cell) → Memo → BM (Memo × List TC)
  | [], memo => pure (memo, [])
  | x :: ps, memo => do
    let sc' ← mulAdd .E sc x.1 z
    let r ← partTerm ν xb z o sc' nu x.2.1 x.2.2 memo
    let r' ← partsTerms ν xb z o sc nu ps r.1
    pure (r'.1, r.2 :: r'.2)

/-- The terms of a claim (scale cell `sc`). -/
def oneClaim (ν xb : Nat) (z o sc : Cell) (cc : CClaim) (memo : Memo) : BM (Memo × List TC) :=
  match cc.cw with
  | .point blk zl => do
    let r ← partTerm ν xb z o sc ν blk zl memo
    pure (r.1, [r.2])
  | .ring blk pt cs => do
    let t ← ringTerm ν xb z sc blk pt cs
    pure (memo, [t])
  | .sum nu parts => partsTerms ν xb z o sc nu parts memo

/-- The terms of the claims from index `i` (scale cells `sp + i`). -/
def claimTerms (ν xb : Nat) (z o : Cell) (sp : Nat) : Nat → List CClaim → Memo → BM (Memo × List TC)
  | _, [], memo => pure (memo, [])
  | i, cc :: cl, memo => do
    let r ← oneClaim ν xb z o (ec (sp + i)) cc memo
    let r' ← claimTerms ν xb z o sp (i + 1) cl r.1
    pure (r'.1, r.2 ++ r'.2)

/-- Static well-formedness of one claim. -/
def WF1 (ν : Nat) (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk zl => decide (blk.variableCount ≤ ν) && decide (zl.length = blk.variableCount)
  | .ring blk pt cs => decide (blk.variableCount ≤ ν) && decide (pt.length = blk.variableCount) &&
      decide (cs.length = 64) && decide (sz (binDec 64 blk.variableCount 0) = blk.variableCount)
  | .sum nu parts => decide (nu ≤ ν) &&
      parts.all fun x => decide (x.2.1.variableCount ≤ nu) && decide (x.2.2.length = x.2.1.variableCount)

/-- Static well-formedness of the claims for a stack of `ν` variables (cheap to decide on ≈ 3 k claims). -/
def ClaimsWF (ν : Nat) (cl : List CClaim) : Bool := cl.all (WF1 ν)

/-- The batched weight `Σ_i s^i · onStack_i(x)` at the point in the `E` cells `xb + i`, `i < ν`. -/
def basisG (ν : Nat) (cl : List CClaim) (sp xb : Nat) (z o _g : Cell) : BM Cell := do
  let r ← claimTerms ν xb z o sp 0 cl []
  trieG xb z ν r.2

/-! ## Specs -/

section
variable {ν xb : Nat} {z o : Cell}

theorem partTerm_spec (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {nu : Nat} {blk : Placement}
    {zl : List Cell} {memo : Memo} (hm : MemoOk M (fun i => M.e (xb + i)) memo)
    (hzl : zl.length = blk.variableCount) (hvc : blk.variableCount ≤ nu) (hnu : nu ≤ ν) :
    Hs c M (partTerm ν xb z o sc nu blk zl memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      tval M (fun i => M.e (xb + i)) ν r.2 = sc.val M * (e0f M ν xb nu * partW M ν xb nu blk zl)) :=
  hs_bind (chainG_spec hz ho _ memo (ncPre_le z o zl) hm) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', by
    rw [tval, kprod_keyOf, hv, ← partW_eq hz ho hzl hvc hnu]
    ring⟩

theorem zval_e (hz : z.val M = 0) (hzE : z.ty = .E) : M.e z.n = 0 := by
  rw [← hz]; rcases z with ⟨ty, n⟩; cases hzE; rfl

theorem ringTerm_spec (hz : z.val M = 0) (hzE : z.ty = .E) {sc : Cell} {blk : Placement} {pt cs : List Cell}
    (hvc : blk.variableCount ≤ ν) (hpt : pt.length = blk.variableCount) (hcs : cs.length = 64)
    (hbs : sz (binDec 64 blk.variableCount 0) = blk.variableCount) :
    Hs c M (ringTerm ν xb z sc blk pt cs) (fun t => tval M (fun i => M.e (xb + i)) ν t =
      sc.val M * (blk.eqAbove (xsOf M ν xb) *
        ringWeight (vs M pt) ((xsOf M ν xb).take blk.variableCount) (vs M cs))) :=
  hs_bind (ringLeaf_spec (zval_e hz hzE) hpt hcs hbs ((xsOf M ν xb).take blk.variableCount)
    (by rw [List.length_take, xs_length]; (clear * - hvc hpt hbs; omega))
    (fun n hn => by rw [getD_take' _ _ hn, xs_getD (by (clear * - hvc hpt hbs hn; omega))])) fun lf hlf => hs_pure (by
    rw [tval, kprod_keyOf, hlf, eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hvc)
      (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring)

theorem partsTerms_spec (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {nu : Nat} (hnu : nu ≤ ν) :
    ∀ (ps : List (Cell × Placement × List Cell)) (memo : Memo),
      (ps.all fun x => decide (x.2.1.variableCount ≤ nu) && decide (x.2.2.length = x.2.1.variableCount)) = true →
      MemoOk M (fun i => M.e (xb + i)) memo →
      Hs c M (partsTerms ν xb z o sc nu ps memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          sc.val M * (e0f M ν xb nu * (ps.map fun x => x.1.val M * partW M ν xb nu x.2.1 x.2.2).sum))
  | [], memo, _, hm => hs_pure ⟨hm, by simp⟩
  | x :: ps, memo, hwf, hm => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨h1, h2⟩, hrest⟩ := hwf
    show Hs c M (mulAdd .E sc x.1 z >>= fun sc' => partTerm ν xb z o sc' nu x.2.1 x.2.2 memo >>= fun r =>
      partsTerms ν xb z o sc nu ps r.1 >>= fun r' => pure (r'.1, r.2 :: r'.2)) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun sc' hsc => hs_bind (partTerm_spec hz ho hm h2 h1 hnu)
      fun r ⟨hm', hv⟩ => hs_bind (partsTerms_spec hz ho hnu ps r.1 hrest hm') fun r' ⟨hm'', hv'⟩ =>
        hs_pure ⟨hm'', ?_⟩
    rw [List.map_cons, List.sum_cons, hv, hv', hsc, hz, List.map_cons, List.sum_cons]
    ring

theorem sumE_eq (l : List FE) : sumE l = l.sum := by
  rw [sumE, foldl_add_id, zero_add]

/-- A sum claim's weight on the stack. -/
theorem sum_onStack (nu : Nat) (parts : List (Cell × Placement × List Cell)) (com : Com) (v : Cell)
    (xs : List FE) :
    ((⟨com, .sum nu parts, v⟩ : CClaim).val M).2.onStack.1 xs =
      (⟨nu, 0⟩ : Placement).eqAbove xs * (parts.map fun x => x.1.val M *
        (x.2.1.eqAbove (xs.take nu) * eqEval (vs M x.2.2) ((xs.take nu).take x.2.1.variableCount))).sum := by
  simp only [CClaim.val, sumClaim, BlockClaim.onStack, sumE_eq, List.map_map]
  refine congrArg (_ * ·) (congrArg List.sum (List.map_congr_left fun x _ => ?_))
  rcases x with ⟨k, blk, zl⟩
  simp only [Function.comp_apply]
  ring

theorem oneClaim_spec (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sc : Cell} {cc : CClaim}
    {memo : Memo} (hwf : WF1 ν cc = true) (hm : MemoOk M (fun i => M.e (xb + i)) memo) :
    Hs c M (oneClaim ν xb z o sc cc memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = sc.val M * (cc.val M).2.onStack.1 (xsOf M ν xb)) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    show Hs c M (partTerm ν xb z o sc ν blk zl memo >>= fun r => pure (r.1, [r.2])) _
    refine hs_bind (partTerm_spec hz ho hm hwf.2 hwf.1 le_rfl) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', ?_⟩
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hv, e0f, partW, Finset.Ico_self,
      Finset.prod_empty, List.take_of_length_le (by rw [xs_length])]
    show _ = sc.val M * (blk.eqAbove (xsOf M ν xb) * eqEval (vs M zl) ((xsOf M ν xb).take blk.variableCount))
    ring
  | ring blk pt cs =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hwf
    show Hs c M (ringTerm ν xb z sc blk pt cs >>= fun t => pure (memo, [t])) _
    refine hs_bind (ringTerm_spec hz hzE h1 h2 h3 h4) fun t ht => hs_pure ⟨hm, ?_⟩
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ht]
    rfl
  | sum nu parts =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    show Hs c M (partsTerms ν xb z o sc nu parts memo) _
    refine hs_mono (partsTerms_spec hz ho hwf.1 parts memo hwf.2 hm) fun r ⟨hm', hv⟩ => ⟨hm', ?_⟩
    rw [hv, sum_onStack, eqAbove_prod ⟨nu, 0⟩ _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hwf.1)
      (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    have e0 : ∏ i ∈ Finset.Ico nu ν, fb (selbit ⟨nu, 0⟩ i) (M.e (xb + i)) = e0f M ν xb nu :=
      Finset.prod_congr rfl fun i _ => by simp [selbit, fb]
    rw [e0]
    exact congrArg (_ * ·) (congrArg (_ * ·) (congrArg List.sum (List.map_congr_left fun x _ => rfl)))

theorem claimTerms_spec (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sp N : Nat} {s : FE}
    (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (cl : List CClaim) (i : Nat) (memo : Memo), cl.all (WF1 ν) = true →
      MemoOk M (fun i => M.e (xb + i)) memo → i + cl.length ≤ N →
      Hs c M (claimTerms ν xb z o sp i cl memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          bsum s i (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb)))
  | [], _, memo, _, hm, _ => hs_pure ⟨hm, by simp [bsum]⟩
  | cc :: cl, i, memo, hwf, hm, hN => by
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    simp only [List.length_cons] at hN
    show Hs c M (oneClaim ν xb z o (ec (sp + i)) cc memo >>= fun r =>
      claimTerms ν xb z o sp (i + 1) cl r.1 >>= fun r' => pure (r'.1, r.2 ++ r'.2)) _
    refine hs_bind (oneClaim_spec hz ho hzE hwf.1 hm) fun r ⟨hm', hv⟩ =>
      hs_bind (claimTerms_spec hz ho hzE hs cl (i + 1) r.1 hwf.2 hm' (by (clear * - hN; omega))) fun r' ⟨hm'', hv'⟩ =>
        hs_pure ⟨hm'', ?_⟩
    rw [List.map_append, List.sum_append, hv, hv', List.map_cons, bsum, Cell.val_E, hs i (by (clear * - hN; omega))]

end

/-- **The batched basis**: the cell is `F`'s `dot (powers s n) (claims.map (·.onStack.1 x))`. -/
theorem basisG_spec {ν : Nat} {cl : List CClaim} {sp xb : Nat} {z o g : Cell} {p : Ptr}
    (h : SegsHold c M p (basisG ν cl sp xb z o g p).2) (hwf : ClaimsWF ν cl = true)
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (_hoE : o.ty = .E) (_hg : g.ty = .K) (s : FE) (hs : ∀ i < cl.length, M.e (sp + i) = s ^ i) :
    (basisG ν cl sp xb z o g p).1.val M =
      Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.onStack.1 ((List.range ν).map fun i => M.e (xb + i))) := by
  have key := hs_bind (claimTerms_spec (c := c) (ν := ν) (xb := xb) hz ho hzE hs cl 0 [] hwf
    (fun _ he => by simp at he) (by (clear * -; omega))) fun r ⟨_, hv⟩ =>
      hs_mono (trieG_spec (c := c) (xb := xb) hz ν r.2) fun w hw => hw.trans hv
  have e := key p h
  rw [show (basisG ν cl sp xb z o g p).1 = ((claimTerms ν xb z o sp 0 cl [] >>= fun r => trieG xb z ν r.2) p).1
    from rfl, e]
  show _ = Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb))
  have hl : cl.length = (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb)).length := by simp
  rw [hl, dot_powers_bsum]

end Lvm.Har
