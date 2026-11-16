-- New for lvm (HAR-WH): Q_arith phases 8–9 (the stacked WHIR openings of `C_rec` and `C_main`): the
-- stream layout of one opening, `F`'s values as pure functions of the stream, and the level gadgets
-- (rounds, glue, row folds with the enforced sum, column weights, constants, the final weight sum),
-- wiring QA2's gadgets (`LvmQWhir*`).
import LvmQAsmHarBase
import LvmQWhirBatch
import LvmQRingWeight
import LvmQWhirFold

-- ===== merged from `LvmQWhirWeight` (GOLF module merge: `LvmQWhirWeight.lean` is now a stub importing `LvmQAsmArith2WhirG`) =====
section

/-!
# QA2: WHIR column weights (`inducedWeight`) as builder gadgets

`F`'s glued weight of a level (`LvmDecideWhir.inducedWeight`, leanVM `induced_weight`):
`Σ_q w_q · Π_k (1 + p_k (1 + W_k(x_q) · inv_k))` with the subspace-polynomial chain
`W_0 = x_q`, `W_{k+1} = W_k² + R_k W_k` (`R` = `subspaceRoots`, `inv` their inverses).

**The F side** (`inducedWeight_eq`): the outer fold is a sum over the positions of `iwSeq … κ`,
the inner fold after `κ = |point|` coordinates (`iwSeq`, one `iwStep` per coordinate).

**The circuit** (`colWeight`), for `2^a` positions and the coordinates cut into chunks `2^c_i`
(`Σ 2^c_i = κ`):
* constants, per coordinate `k` (`E` cells at `cb + 2k`, `cb + 2k + 1`): `A_k = 1 + p_k`,
  `B_k = p_k · I_k` (`I_k` a `K` cell holding `inv_k`);
* prologue (loop `[a]`): `acc_q = w_q`, `W_q = x_q` (copies, laid out as the main loop's carried rows);
* per chunk a loop of dims `[a, c]` (**position inner, coordinate outer**), four rows:
  `f = B_k · W + A_k` (E·K), `acc' = acc · f` (E·E), `u = W + R_k` (K lin), `W' = W · u` (K muladd); the
  carried `acc`, `W` are read at offset `−2·2^a` (the previous coordinate, or the prologue);
* the sum over positions (loop `[a]`, running `lin`) and one difference row.
Cost per (position, coordinate): 14 + 16 + 6 + 8 = 44 words.

Reuse: leanerVM `Protocol/NovelBasis.lean` (`vanish`: `V_{k+1} = V_k (V_k + root_k)`, `normW`)
states the same chain; restated here on `Lvm.FE` against `F`'s own definitions.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-! ## The F side -/

/-- One coordinate of `inducedWeight`'s inner fold (`LvmDecideWhir:54-56`). -/
def iwStep (R I : List FE) (acc : FE × FE) (ck : FE × Nat) : FE × FE :=
  (acc.1 * (1 + ck.1 * (1 + acc.2 * I.getD ck.2 0)), FE.sq acc.2 + R.getD ck.2 0 * acc.2)

/-- The inner fold after `k` coordinates. -/
def iwSeq (R I pt : List FE) (w x : FE) : Nat → FE × FE
  | 0 => (w, x)
  | k + 1 => iwStep R I (iwSeq R I pt w x k) (pt.getD k 0, k)

theorem iwSeq_congr (R I : List FE) (w x : FE) {pt pt' : List FE} :
    ∀ k, (∀ j < k, pt.getD j 0 = pt'.getD j 0) → iwSeq R I pt w x k = iwSeq R I pt' w x k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [iwSeq]
    rw [iwSeq_congr R I w x k (fun j hj => h j (by (clear * - hj; omega))), h k (by (clear * -; omega))]

theorem foldl_zipIdx_eq (R I : List FE) (w x : FE) : ∀ (pt : List FE),
    pt.zipIdx.foldl (iwStep R I) (w, x) = iwSeq R I pt w x pt.length := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.zipIdx_append, List.foldl_append, ih]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton, iwSeq, Nat.zero_add]
    rw [iwSeq_congr R I w x (pt := l ++ [a]) (pt' := l) l.length
      (fun j hj => by rw [List.getD_append _ _ _ _ hj])]
    simp

theorem foldl_add_map {α : Type} (g : α → FE) : ∀ (l : List α) (a : FE),
    l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_map g l]; simp [add_assoc]

/-- The roots and inverses `inducedWeight` uses. -/
def iwRoots (m : Nat) : List FE := subspaceRoots m

/-- The inverses `inducedWeight` uses. -/
def iwInvs (m : Nat) : List FE := (subspaceRoots m).map fun v => if v == 0 then 0 else v⁻¹

/-- **`inducedWeight` as a sum over the positions** of the inner fold after `|point|`
coordinates (`x_q = eOfNat q`). -/
theorem inducedWeight_eq (m : Nat) (qs : List Nat) (ws pt : List FE) :
    inducedWeight m qs ws pt = ((List.zip ws qs).map fun wq =>
      (iwSeq (iwRoots m) (iwInvs m) pt wq.1 (eOfNat wq.2) pt.length).1).sum := by
  show List.foldl (fun total x => total +
      (List.foldl (iwStep (iwRoots m) (iwInvs m)) (x.1, eOfNat x.2) pt.zipIdx).1) 0 (ws.zip qs) = _
  rw [foldl_add_map (fun x : FE × Nat =>
      (List.foldl (iwStep (iwRoots m) (iwInvs m)) (x.1, eOfNat x.2) pt.zipIdx).1), zero_add]
  congr 1
  apply List.map_congr_left
  intro wq _
  rw [foldl_zipIdx_eq]

/-! ## The circuit -/

/-- Constants of coordinates `[k₀, k₀ + 2^c)`: `A_k = 1 + p_k`, `B_k = p_k · I_k` (`p_k` the `E`
cell `ptb + k`, `I_k` the `K` cell `ib + k`, `z` an `E` zero cell). -/
def cwConsts (c k₀ ptb ib z : Nat) : BM LoopOut :=
  loop [c] [⟨.lin 0 1, .E, [.abs ⟨.E, ptb + k₀, [1]⟩, .abs ⟨.E, ptb + k₀, [1]⟩]⟩,
    ⟨.muladd, .E, [.abs ⟨.E, ptb + k₀, [1]⟩, .abs ⟨.K, ib + k₀, [1]⟩, .abs ⟨.E, z, [0]⟩]⟩]

/-- The prologue: `acc_q = w_q` (`E` cell `wb + q`), `W_q = x_q` (`K` cell `xb + q`), each after a
padding row so that they sit where the main loop's carried rows do. -/
def cwPro (a wb xb : Nat) : BM LoopOut :=
  loop [a] [⟨.lin 0 0, .E, [.abs ⟨.E, wb, [1]⟩, .abs ⟨.E, wb, [1]⟩]⟩,
    ⟨.lin 0 0, .E, [.abs ⟨.E, wb, [1]⟩, .abs ⟨.E, wb, [1]⟩]⟩,
    ⟨.lin 0 0, .K, [.abs ⟨.K, xb, [1]⟩, .abs ⟨.K, xb, [1]⟩]⟩,
    ⟨.lin 0 0, .K, [.abs ⟨.K, xb, [1]⟩, .abs ⟨.K, xb, [1]⟩]⟩]

/-- The template of a chunk at pointer `p`: coordinates `k₀ + k`, constants at `cb + 2k`, roots
`R_k` at the `K` cells `rb + k₀ + k`. -/
def cwTpl (a k₀ cb rb z zk : Nat) (p : Ptr) : List LRow :=
  [⟨.muladd, .E, [.abs ⟨.E, cb + 2 * k₀ + 1, [0, 2]⟩, .abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩,
      .abs ⟨.E, cb + 2 * k₀, [0, 2]⟩]⟩,
   ⟨.muladd, .E, [.abs ⟨.E, p.e + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .cur 0, .abs ⟨.E, z, [0, 0]⟩]⟩,
   ⟨.lin 1 0, .K, [.abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .abs ⟨.K, rb + k₀, [0, 1]⟩]⟩,
   ⟨.muladd, .K, [.abs ⟨.K, p.k + 1 - 2 * 2 ^ a, [2, 2 * 2 ^ a]⟩, .cur 2, .abs ⟨.K, zk, [0, 0]⟩]⟩]

/-- The chunks: coordinates `[k₀, k₀ + Σ 2^c)`. -/
def cwChunks (a cb rb z zk : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | k₀, cc :: cs => fun p =>
    ((), (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2 ++
      (cwChunks a cb rb z zk (k₀ + 2 ^ cc) cs (p.adv (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2)).2)

/-- The constants of every chunk, contiguous: `A_k`, `B_k` at `p.e + 2k`, `p.e + 2k + 1`. -/
def cwConstsAll (ptb ib z : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | k₀, cc :: cs => fun p =>
    ((), (cwConsts cc k₀ ptb ib z p).2 ++
      (cwConstsAll ptb ib z (k₀ + 2 ^ cc) cs (p.adv (cwConsts cc k₀ ptb ib z p).2)).2)

/-- The sum over the positions of the carried `acc` cells at `base + 2q` (running `lin`, then the
difference with the cell before the loop). -/
def cwSum (a n base : Nat) : BM Cell := do
  let p ← getPtr
  let s ← loop [a] [⟨.lin 1 0, .E, [.abs ⟨.E, base, [2]⟩, .prev 0]⟩]
  add (s.cell 0 (n - 1)) (ec (p.e - 1))

/-- **The column weight of one level** over `n ≤ 2^a` positions (the loops run `2^a`, the sum stops
at `n`) (weights `w_q` at `E` cells `wb + q`,
points `x_q` at `K` cells `xb + q`) and the coordinates in chunks `cs` (point coordinates at the
`E` cells `ptb + k`, roots and inverses at the `K` cells `rb + k`, `ib + k`; `z`, `zk` zero cells). -/
def colWeight (a n : Nat) (cs : List Nat) (ptb ib rb wb xb z zk : Nat) : BM Cell := do
  let p ← getPtr
  cwConstsAll ptb ib z 0 cs
  let _ ← cwPro a wb xb
  cwChunks a p.e rb z zk 0 cs
  let p' ← getPtr
  cwSum a n (p'.e + 1 - 2 * 2 ^ a)

variable {c : Ctx} {M : Mem}

theorem unflat_qk {a c q k : Nat} (hq : q < 2 ^ a) (hk : k < 2 ^ c) :
    unflat [a, c] (q + 2 ^ a * k) = [q, k] := unflat_two hq hk

/-- The four row equations of a chunk at position `q`, coordinate `k`. -/
theorem cwChunk_rows {p : Ptr} {a cc k₀ cb rb z zk : Nat}
    (h : SegsHold c M p (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2) {q k : Nat} (hq : q < 2 ^ a)
    (hk : k < 2 ^ cc) :
    M.e (p.e + 2 * (q + 2 ^ a * k)) = M.e (cb + 2 * k₀ + 1 + 2 * k) *
        FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) + M.e (cb + 2 * k₀ + 2 * k) ∧
    M.e (p.e + 1 + 2 * (q + 2 ^ a * k)) =
      M.e (p.e + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k)) * M.e (p.e + 2 * (q + 2 ^ a * k)) + M.e z ∧
    FE.ofK (M.k (p.k + 2 * (q + 2 ^ a * k))) =
      FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) + FE.ofK (M.k (rb + k₀ + k)) ∧
    FE.ofK (M.k (p.k + 1 + 2 * (q + 2 ^ a * k))) =
      FE.ofK (M.k (p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * k))) *
        FE.ofK (M.k (p.k + 2 * (q + 2 ^ a * k))) + FE.ofK (M.k zk) := by
  have hjf : q + 2 ^ a * k < 2 ^ [a, cc].sum := by
    have := lt_size_la hq hk; simpa using this
  have hu := unflat_qk hq hk
  have r0 := loop_rel h (jf := q + 2 ^ a * k) (t := 0) hjf (by simp [cwTpl])
  have r1 := loop_rel h (jf := q + 2 ^ a * k) (t := 1) hjf (by simp [cwTpl])
  have r2 := loop_rel h (jf := q + 2 ^ a * k) (t := 2) hjf (by simp [cwTpl])
  have r3 := loop_rel h (jf := q + 2 ^ a * k) (t := 3) hjf (by simp [cwTpl])
  simp only [LRel, cwTpl, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0 r1 r2 r3
  rw [Opd.val_cur M _ hjf] at r1 r3
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, LoopOut.cell_val,
    Mem.rd_E, Mem.rd_K] at r0 r1 r2 r3
  rw [ofK_one, ofK_zero, one_mul, add_zero] at r2
  exact ⟨r0, r1, r2, r3⟩

/-- The values a chunk carries: `acc` and `W` of position `q` after `k` coordinates, at the cells
`base + 2q + 2·2^a·k` (`base` = the carried rows' first cells, one coordinate before the chunk). -/
def CwAt (M : Mem) (R I pt : List FE) (w x : Nat → FE) (a be bk k₀ k : Nat) : Prop :=
  ∀ q < 2 ^ a, M.e (be + (2 * q + 2 * 2 ^ a * k)) = (iwSeq R I pt (w q) (x q) (k₀ + k)).1 ∧
    FE.ofK (M.k (bk + (2 * q + 2 * 2 ^ a * k))) = (iwSeq R I pt (w q) (x q) (k₀ + k)).2

/-- **A chunk advances the carried values** by its `2^cc` coordinates. -/
theorem cwChunk_spec {p : Ptr} {a cc k₀ cb rb z zk : Nat} {R I pt : List FE} {w x : Nat → FE}
    (h : SegsHold c M p (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2)
    (hpe : 2 * 2 ^ a ≤ p.e) (hpk : 2 * 2 ^ a ≤ p.k) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hA : ∀ k < 2 ^ cc, M.e (cb + 2 * k₀ + 2 * k) = 1 + pt.getD (k₀ + k) 0)
    (hB : ∀ k < 2 ^ cc, M.e (cb + 2 * k₀ + 1 + 2 * k) = pt.getD (k₀ + k) 0 * I.getD (k₀ + k) 0)
    (hR : ∀ k < 2 ^ cc, FE.ofK (M.k (rb + k₀ + k)) = R.getD (k₀ + k) 0)
    (hin : CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ 0) :
    ∀ k ≤ 2 ^ cc, CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ k := by
  intro k hk
  induction k with
  | zero => exact hin
  | succ k ih =>
    intro q hq
    obtain ⟨r0, r1, r2, r3⟩ := cwChunk_rows h hq (k := k) (by omega)
    obtain ⟨ha, hw⟩ := ih (by omega) q hq
    have m : 2 * 2 ^ a * (k + 1) = 2 * (2 ^ a * k) + 2 * 2 ^ a := by ring
    have m' : 2 * 2 ^ a * k = 2 * (2 ^ a * k) := by ring
    have e1 : p.e + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * (k + 1)) = p.e + 1 + 2 * (q + 2 ^ a * k) := by
      rw [m]; omega
    have e2 : p.k + 1 - 2 * 2 ^ a + (2 * q + 2 * 2 ^ a * (k + 1)) = p.k + 1 + 2 * (q + 2 ^ a * k) := by
      rw [m]; omega
    rw [e1, e2, r1, r3, r2, r0, ha, hw, hz, hzk, ofK_zero, hA k (by omega), hB k (by omega),
      hR k (by omega), show k₀ + (k + 1) = (k₀ + k) + 1 by ring]
    simp only [iwSeq, iwStep, FE.sq_eq_mul]
    constructor <;> ring

/-! ### Pointer advances -/

/-- The total number of coordinates of a chunk list. -/
def csum (cs : List Nat) : Nat := (cs.map (2 ^ ·)).sum

theorem csum_cons (cc : Nat) (cs : List Nat) : csum (cc :: cs) = 2 ^ cc + csum cs := by
  simp [csum]

/-! ### Constants -/

theorem cwConsts_spec {p : Ptr} {cc k₀ ptb ib z : Nat} (h : SegsHold c M p (cwConsts cc k₀ ptb ib z p).2)
    {k : Nat} (hk : k < 2 ^ cc) :
    M.e (p.e + 2 * k) = 1 + M.e (ptb + k₀ + k) ∧
      M.e (p.e + 2 * k + 1) = M.e (ptb + k₀ + k) * FE.ofK (M.k (ib + k₀ + k)) + M.e z := by
  have hjf : k < 2 ^ [cc].sum := by simpa using hk
  have hu : unflat [cc] k = [k] := by simp [unflat, Nat.mod_eq_of_lt hk]
  have r0 := loop_rel h (jf := k) (t := 0) hjf (by simp)
  have r1 := loop_rel h (jf := k) (t := 1) hjf (by simp)
  simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0 r1
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K] at r0 r1
  rw [ofK_zero, ofK_one, zero_mul, add_zero] at r0
  refine ⟨by rw [r0]; ring_nf, by rw [show p.e + 2 * k + 1 = p.e + 1 + 2 * k by ring, r1]⟩

theorem cwConstsAll_adv (ptb ib z : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    p.adv (cwConstsAll ptb ib z k₀ cs p).2 = ⟨p.k, p.e + 2 * csum cs⟩
  | [], _, p => by simp [cwConstsAll, pure_apply, csum]
  | cc :: cs, k₀, p => by
    simp only [cwConstsAll, Ptr.adv_append, cwConstsAll_adv ptb ib z cs, cwConsts, loop_adv, csum_cons]
    simp [ltw, LRow.w, Row.w, Row.writes]; ring

theorem cwConstsAll_spec (ptb ib z : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    SegsHold c M p (cwConstsAll ptb ib z k₀ cs p).2 → ∀ k < csum cs,
      M.e (p.e + 2 * k) = 1 + M.e (ptb + k₀ + k) ∧
        M.e (p.e + 2 * k + 1) = M.e (ptb + k₀ + k) * FE.ofK (M.k (ib + k₀ + k)) + M.e z
  | [], _, _, _, k, hk => by simp [csum] at hk
  | cc :: cs, k₀, p, h, k, hk => by
    simp only [cwConstsAll] at h
    rw [segsHold_append] at h
    rw [csum_cons] at hk
    by_cases hlt : k < 2 ^ cc
    · exact cwConsts_spec h.1 hlt
    · have ih := cwConstsAll_spec ptb ib z cs (k₀ + 2 ^ cc) _ h.2 (k - 2 ^ cc) (by (clear * - hk hlt; omega))
      have ha : (p.adv (cwConsts cc k₀ ptb ib z p).2).e = p.e + 2 * 2 ^ cc := by
        simp [cwConsts, loop_adv, ltw, LRow.w, Row.w, Row.writes]
      rw [ha] at ih
      have e1 : p.e + 2 * 2 ^ cc + 2 * (k - 2 ^ cc) = p.e + 2 * k := by (clear * - hlt; omega)
      have e2 : ptb + (k₀ + 2 ^ cc) + (k - 2 ^ cc) = ptb + k₀ + k := by (clear * - e1; omega)
      have e3 : ib + (k₀ + 2 ^ cc) + (k - 2 ^ cc) = ib + k₀ + k := by (clear * - e1; omega)
      rw [e1, e2, e3] at ih
      exact ih

/-! ### Prologue, chunks, sum -/

theorem cwPro_adv (a wb xb : Nat) (p : Ptr) :
    p.adv (cwPro a wb xb p).2 = ⟨p.k + 2 * 2 ^ a, p.e + 2 * 2 ^ a⟩ := by
  simp [cwPro, loop_adv, ltw, LRow.w, Row.w, Row.writes]

theorem cwPro_spec {p : Ptr} {a wb xb : Nat} (h : SegsHold c M p (cwPro a wb xb p).2) {q : Nat}
    (hq : q < 2 ^ a) :
    M.e (p.e + 1 + 2 * q) = M.e (wb + q) ∧ M.k (p.k + 1 + 2 * q) = M.k (xb + q) := by
  have hjf : q < 2 ^ [a].sum := by simpa using hq
  have hu : unflat [a] q = [q] := by simp [unflat, Nat.mod_eq_of_lt hq]
  have r1 := loop_rel h (jf := q) (t := 1) hjf (by simp [cwPro])
  have r3 := loop_rel h (jf := q) (t := 3) hjf (by simp [cwPro])
  simp only [cwPro, LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r1 r3
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K,
    ofK_zero] at r1 r3
  exact ⟨by rw [← r1], ofK_inj (by rw [← r3])⟩

theorem cwChunks_adv (a cb rb z zk : Nat) : ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr),
    p.adv (cwChunks a cb rb z zk k₀ cs p).2 =
      ⟨p.k + 2 * 2 ^ a * csum cs, p.e + 2 * 2 ^ a * csum cs⟩
  | [], _, p => by simp [cwChunks, pure_apply, csum]
  | cc :: cs, k₀, p => by
    simp only [cwChunks, Ptr.adv_append, cwChunks_adv a cb rb z zk cs, loop_adv, csum_cons]
    simp [cwTpl, ltw, LRow.w, Row.w, Row.writes, pow_add]; constructor <;> ring

theorem CwAt.shift {R I pt : List FE} {w x : Nat → FE} {a be bk k₀ n : Nat}
    (h : CwAt M R I pt w x a be bk k₀ n) :
    CwAt M R I pt w x a (be + 2 * 2 ^ a * n) (bk + 2 * 2 ^ a * n) (k₀ + n) 0 := by
  intro q hq
  have := h q hq
  simp only [Nat.mul_zero, Nat.add_zero] at this ⊢
  rw [show be + 2 * 2 ^ a * n + 2 * q = be + (2 * q + 2 * 2 ^ a * n) by ring,
    show bk + 2 * 2 ^ a * n + 2 * q = bk + (2 * q + 2 * 2 ^ a * n) by ring]
  exact this

/-- **The chunks carry the values through every coordinate.** -/
theorem cwChunks_spec {a cb rb z zk K : Nat} {R I pt : List FE} {w x : Nat → FE}
    (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hA : ∀ k < K, M.e (cb + 2 * k) = 1 + pt.getD k 0)
    (hB : ∀ k < K, M.e (cb + 2 * k + 1) = pt.getD k 0 * I.getD k 0)
    (hR : ∀ k < K, FE.ofK (M.k (rb + k)) = R.getD k 0) :
    ∀ (cs : List Nat) (k₀ : Nat) (p : Ptr), SegsHold c M p (cwChunks a cb rb z zk k₀ cs p).2 →
      k₀ + csum cs ≤ K → 2 * 2 ^ a ≤ p.e → 2 * 2 ^ a ≤ p.k →
      CwAt M R I pt w x a (p.e + 1 - 2 * 2 ^ a) (p.k + 1 - 2 * 2 ^ a) k₀ 0 →
      CwAt M R I pt w x a (p.e + 2 * 2 ^ a * csum cs + 1 - 2 * 2 ^ a)
        (p.k + 2 * 2 ^ a * csum cs + 1 - 2 * 2 ^ a) (k₀ + csum cs) 0
  | [], k₀, p, _, _, _, _, hin => by simpa [csum] using hin
  | cc :: cs, k₀, p, h, hK, hpe, hpk, hin => by
    simp only [cwChunks] at h
    rw [segsHold_append] at h
    rw [csum_cons] at hK ⊢
    have hc := cwChunk_spec (R := R) (I := I) (pt := pt) (w := w) (x := x) h.1 hpe hpk hz hzk
      (fun k hk => by rw [show cb + 2 * k₀ + 2 * k = cb + 2 * (k₀ + k) by ring]; exact hA _ (by (clear * - hK hk; omega)))
      (fun k hk => by
        rw [show cb + 2 * k₀ + 1 + 2 * k = cb + 2 * (k₀ + k) + 1 by ring]; exact hB _ (by (clear * - hK hk; omega)))
      (fun k hk => by rw [show rb + k₀ + k = rb + (k₀ + k) by ring]; exact hR _ (by (clear * - hK hk; omega)))
      hin (2 ^ cc) le_rfl
    have hs := hc.shift
    have hp' : p.adv (loop [a, cc] (cwTpl a k₀ cb rb z zk p) p).2 =
        ⟨p.k + 2 * 2 ^ a * 2 ^ cc, p.e + 2 * 2 ^ a * 2 ^ cc⟩ := by
      rw [loop_adv]; congr 1 <;> simp [cwTpl, ltw, LRow.w, Row.w, Row.writes, pow_add] <;> ring
    have ih := cwChunks_spec hz hzk hA hB hR cs (k₀ + 2 ^ cc) _ h.2 (by (clear * - hK; omega))
      (by rw [hp']; exact le_trans hpe (Nat.le_add_right _ _))
      (by rw [hp']; exact le_trans hpk (Nat.le_add_right _ _))
      (by
        rw [hp']; dsimp only
        have e1 : p.e + 2 * 2 ^ a * 2 ^ cc + 1 - 2 * 2 ^ a = p.e + 1 - 2 * 2 ^ a + 2 * 2 ^ a * 2 ^ cc := by
          (clear * - hpe; omega)
        have e2 : p.k + 2 * 2 ^ a * 2 ^ cc + 1 - 2 * 2 ^ a = p.k + 1 - 2 * 2 ^ a + 2 * 2 ^ a * 2 ^ cc := by
          (clear * - hpk; omega)
        rw [e1, e2]; exact hs)
    rw [hp'] at ih
    dsimp only at ih
    rw [show k₀ + (2 ^ cc + csum cs) = k₀ + 2 ^ cc + csum cs by ring,
      show p.e + 2 * 2 ^ a * (2 ^ cc + csum cs) = p.e + 2 * 2 ^ a * 2 ^ cc + 2 * 2 ^ a * csum cs by ring,
      show p.k + 2 * 2 ^ a * (2 ^ cc + csum cs) = p.k + 2 * 2 ^ a * 2 ^ cc + 2 * 2 ^ a * csum cs by ring]
    exact ih

/-- **The sum over the positions**: `Σ_q acc_q`, `acc_q` the `E` cell `base + 2q`. -/
theorem cwSum_spec {p : Ptr} {a n base : Nat} (h : SegsHold c M p (cwSum a n base p).2) (hp : 1 ≤ p.e)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a) :
    (cwSum a n base p).1.val M = ∑ q ∈ Finset.range n, M.e (base + 2 * q) := by
  simp only [cwSum, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  have hs := lin_spec h.2
  simp only [add] at hs ⊢
  rw [hs]
  have hstep : ∀ x < 2 ^ a, M.e (p.e + 1 * x) = M.e (base + 2 * x) + M.e (p.e - 1 + 1 * x) := by
    intro x hx
    have hjf : x < 2 ^ [a].sum := by simpa using hx
    have hu : unflat [a] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, ofK_one,
      ofK_zero] at r
    simp only [Nat.one_mul]
    rw [r]
  have hpre := prefix_cells M.e p.e 1 (2 ^ a) hp (fun q => M.e (base + 2 * q)) hstep
  have hl := hpre n hna
  simp only [Nat.one_mul] at hl
  have hc : (LoopOut.cell ⟨p, [a], [⟨.lin 1 0, .E, [.abs ⟨.E, base, [2]⟩, .prev 0]⟩]⟩ 0 (n - 1)).val M
      = M.e (p.e - 1 + n) := by
    simp [LoopOut.cell_val, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Mem.rd_E]
    congr 1; omega
  simp only [loop_apply] at hc ⊢
  rw [hc, hl, ofK_one, ofK_zero, one_mul, add_zero, Cell.val_E, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

/-- **The column weight gadget**: its cell is `Σ_q (iwSeq R I pt w_q x_q κ).1`, `κ = csum cs`. -/
theorem colWeight_spec {p : Ptr} {a n : Nat} {cs : List Nat} {ptb ib rb wb xb z zk : Nat}
    (h : SegsHold c M p (colWeight a n cs ptb ib rb wb xb z zk p).2) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a)
    (R I pt : List FE)
    (hpt : ∀ k < csum cs, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < csum cs, FE.ofK (M.k (ib + k)) = I.getD k 0)
    (hR : ∀ k < csum cs, FE.ofK (M.k (rb + k)) = R.getD k 0) :
    (colWeight a n cs ptb ib rb wb xb z zk p).1.val M = ∑ q ∈ Finset.range n,
      (iwSeq R I pt (M.e (wb + q)) (FE.ofK (M.k (xb + q))) (csum cs)).1 := by
  simp only [colWeight, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
    Ptr.adv_nil] at h ⊢
  rw [segsHold_append, segsHold_append, segsHold_append] at h
  obtain ⟨hc, hpr, hch, hs⟩ := h
  rw [cwConstsAll_adv] at hpr hch hs ⊢
  rw [cwPro_adv] at hch hs ⊢
  rw [cwChunks_adv] at hs ⊢
  dsimp only at hch hs ⊢
  have hcon := cwConstsAll_spec ptb ib z cs 0 p hc
  have hA : ∀ k < csum cs, M.e (p.e + 2 * k) = 1 + pt.getD k 0 := fun k hk => by
    rw [(hcon k hk).1, Nat.add_zero, hpt k hk]
  have hB : ∀ k < csum cs, M.e (p.e + 2 * k + 1) = pt.getD k 0 * I.getD k 0 := fun k hk => by
    rw [(hcon k hk).2, Nat.add_zero, Nat.add_zero, hpt k hk, hI k hk, hz, add_zero]
  have hin : CwAt M R I pt (fun q => M.e (wb + q)) (fun q => FE.ofK (M.k (xb + q))) a
      (p.e + 2 * csum cs + 2 * 2 ^ a + 1 - 2 * 2 ^ a) (p.k + 2 * 2 ^ a + 1 - 2 * 2 ^ a) 0 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := cwPro_spec hpr hq
    simp only [Nat.mul_zero, Nat.add_zero, iwSeq]
    rw [show p.e + 2 * csum cs + 2 * 2 ^ a + 1 - 2 * 2 ^ a + 2 * q = p.e + 2 * csum cs + 1 + 2 * q by
      omega, show p.k + 2 * 2 ^ a + 1 - 2 * 2 ^ a + 2 * q = p.k + 1 + 2 * q by omega]
    exact ⟨h1, by rw [h2]⟩
  have hout := cwChunks_spec (c := c) (M := M) (K := csum cs) hz hzk hA hB
    (fun k hk => hR k hk) cs 0 _ hch (by simp) (by dsimp only; omega) (by dsimp only; omega) hin
  rw [cwSum_spec hs (by have := Nat.one_le_two_pow (n := a); dsimp only; omega) hn hna]
  refine Finset.sum_congr rfl fun q hq => ?_
  have := (hout q (lt_of_lt_of_le (Finset.mem_range.mp hq) hna)).1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
  exact this

/-! ## Equivalence with `F` -/

theorem sum_zip_map (g : FE × Nat → FE) : ∀ (ws : List FE) (qs : List Nat), ws.length = qs.length →
    ((ws.zip qs).map g).sum = ∑ i ∈ Finset.range qs.length, g (ws.getD i 0, qs.getD i 0)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | w :: ws, q :: qs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_zip_map g ws qs (by simpa using h), add_comm]

/-- **`inducedWeight` as a sum over the positions** (`Finset` form). -/
theorem inducedWeight_sum (m : Nat) (qs : List Nat) (ws pt : List FE) (h : ws.length = qs.length) :
    inducedWeight m qs ws pt = ∑ i ∈ Finset.range qs.length,
      (iwSeq (iwRoots m) (iwInvs m) pt (ws.getD i 0) (eOfNat (qs.getD i 0)) pt.length).1 := by
  rw [inducedWeight_eq, sum_zip_map _ ws qs h]

/-- **Q_arith_eq, column weights**: the gadget over the positions `[q₀, q₀ + 2^a)` of a level is
their part of `F`'s `inducedWeight m qs ws pt` (`inducedWeight_sum`), when the weight cells hold
`ws`, the position cells hold `x_q = eOfNat q` (`K`), the point cells `pt`, and the constant cells
the roots and inverses of `subspaceRoots m` (`K`-valued: `iwRoots_isK`, `iwInvs_isK`). -/
theorem colWeight_eq {p : Ptr} {a n : Nat} {cs : List Nat} {ptb ib rb wb xb z zk : Nat}
    (h : SegsHold c M p (colWeight a n cs ptb ib rb wb xb z zk p).2) (hz : M.e z = 0) (hzk : M.k zk = 0)
    (hn : 1 ≤ n) (hna : n ≤ 2 ^ a)
    (m q₀ : Nat) (qs : List Nat) (ws pt : List FE) (hκ : csum cs = pt.length)
    (hpt : ∀ k < pt.length, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < pt.length, FE.ofK (M.k (ib + k)) = (iwInvs m).getD k 0)
    (hR : ∀ k < pt.length, FE.ofK (M.k (rb + k)) = (iwRoots m).getD k 0)
    (hw : ∀ q < n, M.e (wb + q) = ws.getD (q₀ + q) 0)
    (hx : ∀ q < n, FE.ofK (M.k (xb + q)) = eOfNat (qs.getD (q₀ + q) 0)) :
    (colWeight a n cs ptb ib rb wb xb z zk p).1.val M = ∑ q ∈ Finset.range n,
      (iwSeq (iwRoots m) (iwInvs m) pt (ws.getD (q₀ + q) 0) (eOfNat (qs.getD (q₀ + q) 0))
        pt.length).1 := by
  rw [colWeight_spec h hz hzk hn hna (iwRoots m) (iwInvs m) pt (hκ ▸ hpt) (hκ ▸ hI) (hκ ▸ hR), hκ]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [hw q (Finset.mem_range.mp hq), hx q (Finset.mem_range.mp hq)]

/-! ## The roots and inverses are `K` values (the constant cells exist) -/

theorem subspaceRootsAux_isK : ∀ (n : Nat) (last : FE) (layer : List FE), Program.IsK last →
    (∀ v ∈ layer, Program.IsK v) → ∀ r ∈ subspaceRootsAux n last layer, Program.IsK r
  | 0, _, _, _, _ => by simp [subspaceRootsAux]
  | n + 1, last, layer, hl, hv => by
    intro r hr
    have hmap : ∀ v ∈ layer.map (fun value => FE.sq value + last * value), Program.IsK v := by
      intro v hv'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv'
      rw [FE.sq_eq_mul]
      exact Program.isK_add (Program.isK_mul (hv u hu) (hv u hu)) (Program.isK_mul hl (hv u hu))
    simp only [subspaceRootsAux] at hr
    split at hr
    · simp at hr
    · next root rest heq =>
      rw [heq] at hmap
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hmap _ (by simp)
      · exact subspaceRootsAux_isK n root rest (hmap _ (by simp))
          (fun v hv => hmap v (by simp [hv])) r hr

theorem isK_zero : Program.IsK 0 := rfl

theorem iwRoots_isK (m k : Nat) : Program.IsK ((iwRoots m).getD k 0) := by
  have hall : ∀ r ∈ iwRoots m, Program.IsK r := by
    intro r hr
    simp only [iwRoots, subspaceRoots] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Program.isK_ofK 1
    · refine subspaceRootsAux_isK m 1 _ (Program.isK_ofK 1) (fun v hv => ?_) r hr
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
      exact Program.isK_ofK _
  rw [List.getD_eq_getElem?_getD]
  cases h : (iwRoots m)[k]? with
  | none => exact isK_zero
  | some r => exact hall r (List.mem_of_getElem? h)

theorem isK_inv {v : FE} (hv : Program.IsK v) : Program.IsK v⁻¹ := by
  unfold Program.IsK at hv ⊢
  have e : (FE.ofK v.c₀)⁻¹ = FE.ofK v.c₀⁻¹ := (map_inv₀ Lvm.FE.ofKRingHom v.c₀).symm
  rw [← hv, e]
  rfl

theorem iwInvs_isK (m k : Nat) : Program.IsK ((iwInvs m).getD k 0) := by
  simp only [iwInvs, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : (subspaceRoots m)[k]? with
  | none => exact isK_zero
  | some r =>
    have := iwRoots_isK m k
    simp only [iwRoots, List.getD_eq_getElem?_getD, h, Option.getD_some] at this
    simp only [Option.map_some, Option.getD_some]
    split
    · exact isK_zero
    · exact isK_inv this

end Lvm.Loop.Build
end
-- ===== end of `LvmQWhirWeight` =====

-- ===== merged from `LvmQWhirClaim` (GOLF module merge: `LvmQWhirClaim.lean` is now a stub importing `LvmQAsmArith2WhirG`) =====
section

/-!
# QA2: column-claim weights at the WHIR terminal point (`eqEval`)

The stacked opening's basis (`LvmDecideWhir.verifyStackedOpening`, `evaluateBasis`) is
`Σ_c s^c · W_c(x)`, and a column claim's weight is `eqAbove · eqEval z (x.take n)`
(`LvmDecideBase.BlockClaim.point`, `onStack`), both products of `eqEval`'s factors
`1 + l_i + r_i`. **`eqEvalG cs lb rb acc`**: `acc · Π_{i < Σ 2^c} (1 + l_i + r_i)` with `l_i`, `r_i`
the `E` cells `lb + i`, `rb + i`; one loop with a prologue per chunk `2^c` of coordinates (a `lin`
and a `muladd` per coordinate, 28 words). `eqEvalG_eq`: with `acc = 1` it is `F`'s `eqEval`.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-- The template of one chunk from coordinate `i₀`. -/
def eeTpl (lb rb i₀ : Nat) (z : Cell) : List LRow :=
  [⟨.lin 1 1, .E, [.abs ⟨.E, lb + i₀, [1]⟩, .abs ⟨.E, rb + i₀, [1]⟩]⟩,
   ⟨.muladd, .E, [.prev 1, .cur 0, z.opd]⟩]

/-- **`acc · Π_i (1 + l_i + r_i)`** over the chunks `cs` of coordinates from `i₀`. -/
def eqEvalG (lb rb : Nat) (z : Cell) : List Nat → Nat → Cell → BM Cell
  | [], _, acc => pure acc
  | cc :: cs, i₀, acc => do
    let o ← loopP [cc] (eeTpl lb rb i₀ z) fun _ => acc
    eqEvalG lb rb z cs (i₀ + 2 ^ cc) (o.cell 1 (2 ^ cc - 1))

variable {c : Ctx} {M : Mem}

theorem eeChunk_spec {cc lb rb i₀ : Nat} {z acc : Cell} {p : Ptr}
    (h : SegsHold c M p (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).2) (hz : z.val M = 0) :
    ∀ x < 2 ^ cc, ((loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1.cell 1 x).val M =
      acc.val M * ∏ i ∈ Finset.range (x + 1), (1 + M.e (lb + i₀ + i) + M.e (rb + i₀ + i)) := by
  have hzv : M.rd z.ty z.n = 0 := hz
  have rows : ∀ x < 2 ^ cc,
      ((loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1.cell 1 x).val M =
        (Opd.prev 1).val M (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1 x *
          (1 + M.e (lb + i₀ + x) + M.e (rb + i₀ + x)) := by
    intro x hx
    have hjf : x < 2 ^ [cc].sum := by simpa using hx
    have hu : unflat [cc] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r0 := loopP_rel h (jf := x) (t := 0) hjf (by simp [eeTpl])
    have r1 := loopP_rel h (jf := x) (t := 1) hjf (by simp [eeTpl])
    generalize ho : (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1 = o at r0 r1 ⊢
    have htpl : o.tpl = eeTpl lb rb i₀ z := by rw [← ho]; rfl
    have hdims : o.dims = [cc] := by rw [← ho]; rfl
    unfold LRel at r0 r1
    simp only [LoopOut.arg, htpl, eeTpl, List.getD_cons_zero, List.getD_cons_succ] at r0 r1
    rw [Opd.val_cur M _ (by rw [hdims]; simpa using hjf)] at r1
    rw [r1, r0]
    simp only [Opd.val_abs, Cell.opd, Cell.addr, Addr.at, hdims, hu, dot, Mem.rd_E, ofK_one, one_mul,
      Nat.add_zero]
    rw [hzv, add_zero]
    ring
  intro x hx
  induction x with
  | zero =>
    rw [rows 0 hx, loopP_prev_zero h (t := 1) (by simp [eeTpl]) (by simp [eeTpl])]
    simp
  | succ x ih =>
    rw [rows (x + 1) hx, loopP_prev_succ M _ _ _ p (by simpa using hx), ih (by omega),
      Finset.prod_range_succ _ (x + 1)]
    ring

theorem eqEvalG_spec (lb rb : Nat) (z : Cell) (hz : z.val M = 0) :
    ∀ (cs : List Nat) (i₀ : Nat) (acc : Cell) (p : Ptr),
      SegsHold c M p (eqEvalG lb rb z cs i₀ acc p).2 →
      (eqEvalG lb rb z cs i₀ acc p).1.val M =
        acc.val M * ∏ i ∈ Finset.range (csum cs), (1 + M.e (lb + i₀ + i) + M.e (rb + i₀ + i))
  | [], _, acc, _, _ => by simp [eqEvalG, pure_apply, csum]
  | cc :: cs, i₀, acc, p, h => by
    simp only [eqEvalG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [eqEvalG_spec lb rb z hz cs _ _ _ h.2, eeChunk_spec h.1 hz _ (by have := Nat.two_pow_pos cc; omega),
      show 2 ^ cc - 1 + 1 = 2 ^ cc by have := Nat.two_pow_pos cc; omega, csum_cons,
      Finset.prod_range_add, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show lb + (i₀ + 2 ^ cc) + i = lb + i₀ + (2 ^ cc + i) by ring,
      show rb + (i₀ + 2 ^ cc) + i = rb + i₀ + (2 ^ cc + i) by ring]

/-- `F`'s `eqEval` as a product. -/
theorem eqEval_prod : ∀ (l r : List FE), l.length = r.length →
    eqEval l r = ∏ i ∈ Finset.range l.length, (1 + l.getD i 0 + r.getD i 0)
  | [], [], _ => by simp [eqEval]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: r, h => by
    have ih := eqEval_prod l r (by simpa using h)
    have key : ∀ (L : List FE) (a : FE), L.foldl (· * ·) a = a * L.foldl (· * ·) 1 := by
      intro L; induction L with
      | nil => simp
      | cons b L ihL => intro a; simp only [List.foldl_cons]; rw [ihL (a * b), ihL (1 * b)]; ring
    simp only [eqEval, List.zipWith_cons_cons, List.foldl_cons, one_mul] at ih ⊢
    rw [key, ih, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- **Q_arith_eq, `eqEval`**: from a cell holding `1`, the gadget is `F`'s `eqEval l r`. -/
theorem eqEvalG_eq {lb rb : Nat} {z one : Cell} {cs : List Nat} {p : Ptr} (l r : List FE)
    (h : SegsHold c M p (eqEvalG lb rb z cs 0 one p).2) (hz : z.val M = 0) (hone : one.val M = 1)
    (hl : l.length = csum cs) (hr : r.length = csum cs)
    (hlc : ∀ i < csum cs, M.e (lb + i) = l.getD i 0) (hrc : ∀ i < csum cs, M.e (rb + i) = r.getD i 0) :
    (eqEvalG lb rb z cs 0 one p).1.val M = eqEval l r := by
  rw [eqEvalG_spec lb rb z hz cs 0 one p h, hone, one_mul, eqEval_prod l r (hl.trans hr.symm), hl]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Nat.add_zero, Nat.add_zero, hlc i (Finset.mem_range.mp hi), hrc i (Finset.mem_range.mp hi)]

end Lvm.Loop.Build
end
-- ===== end of `LvmQWhirClaim` =====

-- ===== merged from `LvmQWhirFinal` (GOLF module merge: `LvmQWhirFinal.lean` is now a stub importing `LvmQAsmArith2WhirG`) =====
section

/-!
# QA2: the WHIR terminal: `multilinearEval` of the residual, and the terminal check

`F`'s final level (`LvmDecideWhir.whirLevels`, `[]` case): `terminal = weight · multilinearEval
residual tailFolds`, `require (terminal == target)`.

* **`mleFold n tb ts rp`**: the residual (`2^n` `E` cells at `tb + ts·v`) folded by the points
  `rp 0 … rp (n−1)` (`F`'s `foldPairs`, one level per coordinate): per pair a `lin` (`a + b`) and a
  `muladd` (`r·(a + b) + a = a(1+r) + br`), 28 words per pair; the levels are loops of dims
  `[n − j − 1]`. `mleFold_spec`: the result is `multilinearEval residual point`.
* **`terminalCheck weight mle target gate`**: `t = weight · mle + target`, `assert0 t gate`:
  with the gate on, the assertion holds iff `weight · mle = target` (`F`'s `terminal == target`).

Cost (P20): C_rec 2^13 residual: 8,191 pairs (229 k words) + its loads; C_main 2^8: 255 pairs.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-! ## The F side -/

/-- One fold of `multilinearEval` as an index function. -/
theorem foldPairs_getD (r : FE) : ∀ (L : List FE) (x : Nat), 2 * x + 1 < L.length →
    (foldPairs r L).getD x 0 = L.getD (2 * x) 0 * (1 + r) + L.getD (2 * x + 1) 0 * r
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: rest, 0, _ => by simp [foldPairs]
  | a :: b :: rest, x + 1, h => by
    simp only [foldPairs, List.getD_cons_succ]
    rw [foldPairs_getD r rest x (by simp at h; omega)]
    congr 2 <;> congr 1 <;> ring

theorem foldPairs_length (r : FE) : ∀ (L : List FE), (foldPairs r L).length = L.length / 2
  | [] => rfl
  | [_] => by simp [foldPairs]
  | a :: b :: rest => by
    simp only [foldPairs, List.length_cons, foldPairs_length r rest]; omega

/-- The residual after `j` folds. -/
def resAfter (res pt : List FE) (j : Nat) : List FE := (pt.take j).foldl (fun cur r => foldPairs r cur) res

theorem resAfter_succ (res pt : List FE) (j : Nat) (hj : j < pt.length) :
    resAfter res pt (j + 1) = foldPairs (pt.getD j 0) (resAfter res pt j) := by
  simp only [resAfter]
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hj]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem resAfter_length (res pt : List FE) (n : Nat) (hres : res.length = 2 ^ n) :
    ∀ j ≤ n, j ≤ pt.length → (resAfter res pt j).length = 2 ^ (n - j) := by
  intro j hj hjp
  induction j with
  | zero => simpa [resAfter] using hres
  | succ j ih =>
    rw [resAfter_succ _ _ _ (by (clear * - hjp; omega)), foldPairs_length, ih (by (clear * - hj; omega)) (by (clear * - hjp; omega))]
    rw [show n - j = (n - (j + 1)) + 1 by (clear * - hj; omega), pow_succ]; simp

theorem multilinearEval_eq (res pt : List FE) (n : Nat) (hres : res.length = 2 ^ n)
    (hpt : pt.length = n) : multilinearEval res pt = (resAfter res pt n).getD 0 0 := by
  simp only [multilinearEval, resAfter]
  rw [← hpt, List.take_length]
  cases h : List.foldl (fun cur r => foldPairs r cur) res pt with
  | nil => rfl
  | cons a l => rfl

/-! ## The circuit -/

/-- The fold levels `j, j+1, …, n−1` from the table at `tb` (stride `ts`, `2^(n−j)` entries). -/
def mleLevels (rp : Nat → Cell) (n : Nat) : (j tb ts : Nat) → (fuel : Nat) → BM Cell
  | _, tb, _, 0 => pure (ec tb)
  | j, tb, ts, fuel + 1 => do
    let p ← getPtr
    let _ ← loop [n - j - 1] [⟨.lin 1 0, .E, [.abs ⟨.E, tb, [2 * ts]⟩, .abs ⟨.E, tb + ts, [2 * ts]⟩]⟩,
      ⟨.muladd, .E, [(rp j).opd, .cur 0, .abs ⟨.E, tb, [2 * ts]⟩]⟩]
    mleLevels rp n (j + 1) (p.e + 1) 2 fuel

/-- **The residual's multilinear evaluation**: load the `2^n` scalars (lanes `lb + 3v + (0,1,2)`),
then fold them by `rp 0, …, rp (n−1)`; the result cell. -/
def mleFold (n lb : Nat) (rp : Nat → Cell) : BM Cell := do
  let p ← getPtr
  let _ ← loop [n] [⟨.loadE, .E, [.abs ⟨.K, lb, [3]⟩, .abs ⟨.K, lb + 1, [3]⟩, .abs ⟨.K, lb + 2, [3]⟩]⟩]
  mleLevels rp n 0 p.e 1 n

variable {c : Ctx} {M : Mem}

theorem mleLevels_spec (rp : Nat → Cell) (n : Nat) (res pt : List FE) (hres : res.length = 2 ^ n)
    (hpt : pt.length = n) (hrp : ∀ j < n, (rp j).val M = pt.getD j 0) :
    ∀ (fuel j tb ts : Nat) (p : Ptr), j + fuel = n →
      SegsHold c M p (mleLevels rp n j tb ts fuel p).2 →
      (∀ x < 2 ^ (n - j), M.e (tb + ts * x) = (resAfter res pt j).getD x 0) →
      (mleLevels rp n j tb ts fuel p).1.val M = (resAfter res pt n).getD 0 0
  | 0, j, tb, ts, p, hj, _, hT => by
    simp only [mleLevels, pure_apply, Cell.val_E]
    have := hT 0 (Nat.two_pow_pos _)
    rw [Nat.add_zero] at hj; subst hj
    simpa using this
  | fuel + 1, j, tb, ts, p, hj, h, hT => by
    simp only [mleLevels, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
    rw [segsHold_append] at h
    apply mleLevels_spec rp n res pt hres hpt hrp fuel (j + 1) (p.e + 1) 2 _ (by (clear * - hj; omega)) h.2
    intro x hx
    have hjf : x < 2 ^ [n - j - 1].sum := by
      simp; rwa [show n - (j + 1) = n - j - 1 by (clear * -; omega)] at hx
    have hu : unflat [n - j - 1] x = [x] := by
      simp [unflat, Nat.mod_eq_of_lt (by simpa using hjf)]
    have r0 := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    have r1 := loop_rel h.1 (jf := x) (t := 1) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs, Cell.opd] at r0 r1
    rw [Opd.val_cur M _ hjf] at r1
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Cell.addr,
      LoopOut.cell_val, ofK_one, ofK_zero] at r0 r1
    have hlen := resAfter_length res pt n hres j (by (clear * - hj; omega)) (by (clear * - hpt hj; omega))
    have hlt : 2 * x + 1 < (resAfter res pt j).length := by
      rw [hlen, show n - j = (n - (j + 1)) + 1 by (clear * - hj; omega), pow_succ]; (clear * - hx; omega)
    rw [resAfter_succ res pt j (by (clear * - hpt hj; omega)), foldPairs_getD _ _ x hlt]
    have ha := hT (2 * x) (by rw [← hlen]; (clear * - hlen hlt; omega))
    have hb := hT (2 * x + 1) (by rw [← hlen]; omega)
    rw [r1, r0, ← hrp j (by (clear * - hj; omega))]
    rw [show tb + 2 * ts * x = tb + ts * (2 * x) by ring, show tb + ts + 2 * ts * x = tb + ts * (2 * x + 1) by
      ring, ha, hb]
    have hrv : M.rd (rp j).ty (rp j).n = (rp j).val M := rfl
    rw [hrv]
    ring

/-- **Q_arith_eq, residual evaluation**: the gadget's cell is `F`'s `multilinearEval res pt`, when
the stream lanes hold the residual's `2^n` scalars and `rp j` holds `pt[j]`. -/
theorem mleFold_eq {p : Ptr} {n lb : Nat} {rp : Nat → Cell} (h : SegsHold c M p (mleFold n lb rp p).2)
    (sig : ByteArray) (res pt : List FE) (hres : res.length = 2 ^ n) (hpt : pt.length = n)
    (hrp : ∀ j < n, (rp j).val M = pt.getD j 0)
    (hS : ∀ v < 2 ^ n, ∀ k < 3, M.k (lb + k + 3 * v) = lane sig (lb + k + 3 * v))
    (hv : ∀ v < 2 ^ n, feAt sig (8 * (lb + 3 * v)) = res.getD v 0) :
    (mleFold n lb rp p).1.val M = multilinearEval res pt := by
  simp only [mleFold, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  rw [multilinearEval_eq res pt n hres hpt]
  refine mleLevels_spec rp n res pt hres hpt hrp n 0 p.e 1 _ (by (clear * -; omega)) h.2 ?_
  intro v hv'
  have hv2 : v < 2 ^ n := by simpa using hv'
  have hjf : v < 2 ^ [n].sum := by simpa using hv2
  have hu : unflat [n] v = [v] := by simp [unflat, Nat.mod_eq_of_lt hv2]
  have r0 := loop_rel h.1 (jf := v) (t := 0) hjf (by simp)
  simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K] at r0
  rw [loadE_eq] at r0
  simp only [Nat.one_mul, resAfter, List.take_zero, List.foldl_nil]
  rw [r0, ← hv v hv2]
  have h0 := hS v hv2 0 (by (clear * -; omega))
  have h1 := hS v hv2 1 (by (clear * -; omega))
  have h2 := hS v hv2 2 (by (clear * -; omega))
  simp only [Nat.add_zero] at h0
  rw [show lb + 1 + 3 * v = lb + 1 + 3 * v from rfl, h0, h1, h2]
  simp only [lane, feAt]
  -- `rw`, not `congr 1`: its `rfl` attempt on `kAt` unfolds the lane reads (31 s)
  rw [show 8 * (lb + 1 + 3 * v) = 8 * (lb + 3 * v) + 8 by ring,
    show 8 * (lb + 2 + 3 * v) = 8 * (lb + 3 * v) + 16 by ring]

/-- **The terminal check**: `t = weight · mle + target`, asserted zero under the gate. -/
def terminalCheck (w m tgt gate : Cell) : BM Unit := do
  let t ← mulAdd .E w m tgt
  assert0 t gate

/-- **Q_arith_eq, terminal check**: with the gate on, the assertion holds iff `F`'s
`terminal == target` (`weight · mle = target`). -/
theorem terminalCheck_iff {p : Ptr} {w m tgt gate : Cell}
    (h : SegsHold c M p (terminalCheck w m tgt gate p).2) (hg : gate.val M = 1) :
    SegsAssert M p (terminalCheck w m tgt gate p).2 ↔ w.val M * m.val M = tgt.val M := by
  simp only [terminalCheck, bind_apply, List.nil_append] at h ⊢
  rw [segsHold_append] at h
  have ht := mulAdd_spec h.1
  rw [segsAssert_append]
  have hrow : SegsAssert M p (mulAdd Ty.E w m tgt p).2 := by
    simp [mulAdd, rowRes, SegsAssert, Program.RowAssert, rowInst]
  constructor
  · intro ha
    have := assert0_spec ha.2
    rw [hg, one_mul, ht] at this
    have h2 : w.val M * m.val M + tgt.val M + tgt.val M = tgt.val M := by rw [this, zero_add]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h2
    exact h2
  · intro he
    refine ⟨hrow, ?_⟩
    simp only [assert0, emit]
    rw [segsAssert_row]
    show M.arg _ 1 * M.arg _ 0 = 0
    rw [rowInst_arg, rowInst_arg]
    show gate.val M * (mulAdd Ty.E w m tgt p).1.val M = 0
    rw [hg, one_mul, ht, he, CharTwo.add_self_eq_zero]

end Lvm.Loop.Build
end
-- ===== end of `LvmQWhirFinal` =====

/-!
# Phases 8–9: layout, `F`'s values, level gadgets

**Layout** (lanes; `F` reads position `8V` at byte `8V + 40`, so a scalar read at position `8V` is
lanes `V + 5, V + 6, V + 7`). One stacked opening at position `8U`: the batching challenge at lane
`U + 5`; `verifyWhir`'s first polynomial at position `8(U + 9)` (lanes `U + 14`, `U + 17`); the
levels from lane `U + 15`. A level from lane `V` (`lvLanes`): fold round `j` at `V + 15 j`
(challenge `+5`, polynomial `+14`, `+17`); the final residual (`2^κ` scalars) or the next cap; the
positions (`⌈t/8⌉` answers); `λ` at `V3 + 5`; the openings from `V4` (row `q` at lane
`V4 + 1 + oStr·q`); the intro polynomial at position `8 V5`; the final level's tail rounds from
`V6`. `chLanes`: every fold and tail challenge in `F`'s order; `stackEndL`: the end lane.

**`F`'s values** (`frQ`, `frC`, `tlT`, `qsAt`): the running quadratic after fold rounds, the fold
challenges, the final target of the tail rounds, the positions of a level: functions of the stream
and the position (the run lemmas are in `LvmQAsmArith2WhirF`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## Layout -/

/-- A level's opening stride in lanes: one leaf entry (`40 + row` bytes) and `path` node entries. -/
def oStr (L : Level) : Nat := (40 + L.row + 104 * L.path) / 8

/-- The lanes of a level. -/
structure LvLanes where
  /-- After the fold rounds. -/
  V1 : Nat
  /-- The positions' first answer (after the residual or the next cap, the OOD items, the grinding). -/
  V2 : Nat
  /-- After the positions. -/
  V3 : Nat
  /-- After `λ`: the rows start at `V4 + 1`. -/
  V4 : Nat
  /-- After the openings. -/
  V5 : Nat
  /-- After the intro polynomial. -/
  V6 : Nat
  /-- After the residual (final level) or the next level's cap. -/
  Vc : Nat
  /-- After the OOD items (JB-L §3: `κ` samples, the answer, the intro polynomial; `= Vc` without). -/
  Vo : Nat

/-- The lanes of level `L` from lane `V` (`nxt`: the next level, `none` for the final level; `g`: the
PoW bits, PI-GRIND: with `g > 0` the separator (9 lanes), the nonce (3), the PoW challenge (9) before
the positions; `ood`: the OOD items after a next cap, JB-L §3). -/
def lvLanes (g : Nat) (ood : Bool) (L : Level) (nxt : Option Level) (V : Nat) : LvLanes :=
  let V1 := V + 15 * L.fold
  let Vc := match nxt with
    | none => V1 + 3 * 2 ^ L.kappa
    | some N => V1 + 4 * 2 ^ N.cap
  let Vo := if ood && nxt.isSome then Vc + 9 * L.kappa + 9 else Vc
  let V2 := if g = 0 then Vo else Vo + 21
  let V3 := V2 + 9 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer)
  let V4 := V3 + 9
  let V5 := V4 + oStr L * L.t
  ⟨V1, V2, V3, V4, V5, V5 + 6, Vc, Vo⟩

/-- The lanes of the fold and tail challenges of the levels from lane `V`, in `F`'s order. -/
def chLanes (g : Nat) (ood : Bool) : List Level → Nat → List Nat
  | [], _ => []
  | L :: rest, V =>
    (List.range L.fold).map (fun j => V + 15 * j + 5) ++
    match rest with
    | [] => (List.range L.kappa).map (fun j => (lvLanes g ood L none V).V6 + 15 * j + 5)
    | N :: rest' => chLanes g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-- The lanes of the levels' positions queries (`8 V2`). -/
def posLanes (g : Nat) (ood : Bool) : List Level → Nat → List Nat
  | [], _ => []
  | L :: rest, V =>
    match rest with
    | [] => [(lvLanes g ood L none V).V2]
    | N :: rest' => (lvLanes g ood L (some N) V).V2 :: posLanes g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-- The lane after the levels from lane `V` (the final level ends with a challenge). -/
def stackEndL (g : Nat) (ood : Bool) : List Level → Nat → Nat
  | [], V => V
  | L :: rest, V =>
    match rest with
    | [] => (lvLanes g ood L none V).V6 + 15 * (L.kappa - 1) + 9
    | N :: rest' => stackEndL g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-! ## `F`'s values -/

/-- The running quadratic after `n` fold rounds from position `P` (bytes). -/
def frQ (sig : ByteArray) : Nat → Nat → List FE → List FE
  | _, 0, q => q
  | P, n + 1, q => frQ sig (P + 120) n
      [feAt sig (P + 112), polyEval q (feAt sig (P + 40)) + feAt sig (P + 136), feAt sig (P + 136)]

/-- The challenges of `n` rounds from position `P`. -/
def frC (sig : ByteArray) (P n : Nat) : List FE := (List.range n).map fun j => feAt sig (P + 120 * j + 40)

/-- The final target of `n ≥ 1` tail rounds from position `P`. -/
def tlT (sig : ByteArray) : Nat → Nat → List FE → FE
  | _, 0, _ => 0
  | P, 1, q => polyEval q (feAt sig (P + 40))
  | P, n + 2, q => tlT sig (P + 120) (n + 1)
      [feAt sig (P + 112), polyEval q (feAt sig (P + 40)) + feAt sig (P + 136), feAt sig (P + 136)]

/-- The positions `F` draws for level `L` at position `P`. -/
def qsAt (sig : ByteArray) (P : Nat) (L : Level) : List Nat := (positionsR L sig ⟨P, 0, true⟩).1

/-! ## Gadgets -/

/-- The scalar in lanes `v, v + 1, v + 2` (`F`'s `feAt sig (8 v)`). -/
def ldEW (v : Nat) : BM Cell := loadE (kc v) (kc (v + 1)) (kc (v + 2))

/-- `polyEval [q₀, q₁, q₂] c = q₀ + c (q₁ + c q₂)`. -/
def pev (q : Cell × Cell × Cell) (c : Cell) : BM Cell := do
  let t ← mulAdd .E c q.2.2 q.2.1
  mulAdd .E c t q.1

/-- The round polynomial `F` reads at position `8 v` with the running claim `cl`:
`(a₀, cl + a₂, a₂)` (`sumcheckRoundPoly 3 cl none`). -/
def rdQ (v : Nat) (cl : Cell) : BM (Cell × Cell × Cell) := do
  let a0 ← ldEW (v + 5)
  let a2 ← ldEW (v + 8)
  let q1 ← add cl a2
  pure (a0, q1, a2)

/-- `n` fold rounds from lane `V`: round `j`'s challenge is the `E` cell `pc + f + j`; the running
quadratic after them. -/
def roundsG (pc : Nat) : Nat → Nat → Nat → Cell × Cell × Cell → BM (Cell × Cell × Cell)
  | _, _, 0, q => pure q
  | f, V, n + 1, q => do
    let cl ← pev q (ec (pc + f))
    let q' ← rdQ (V + 9) cl
    roundsG pc (f + 1) (V + 15) n q'

/-- `n ≥ 1` tail rounds from lane `V` (challenges `pc + f + j`); the final target. -/
def tailG (pc : Nat) : Nat → Nat → Nat → Cell × Cell × Cell → BM Cell
  | _, _, 0, _ => pure (ec 0)
  | f, _, 1, q => pev q (ec (pc + f))
  | f, V, n + 2, q => do
    let cl ← pev q (ec (pc + f))
    let q' ← rdQ (V + 9) cl
    tailG pc (f + 1) (V + 15) (n + 1) q'

/-- The glue of one level: `q + λ·i`. -/
def glueG (lam : Cell) (q i : Cell × Cell × Cell) : BM (Cell × Cell × Cell) := do
  let a ← mulAdd .E lam i.1 q.1
  let b ← mulAdd .E lam i.2.1 q.2.1
  let d ← mulAdd .E lam i.2.2 q.2.2
  pure (a, b, d)

/-- The row folds of a level's positions `[q₀, t)` in chunks of `2^a` positions (`as`): word or
scalar `k` of row `q` at lane `lb + k + S q` / `lb + 3k + S q`, the `eq` table at `er` (reversed at
level 0), each chunk dotted with the query weights at `lp + q`; the enforced sum. -/
def foldsG (lvl0 : Bool) (l lb S er lp t : Nat) (z : Cell) : Nat → List Nat → BM Cell
  | _, [] => pure z
  | q₀, a :: as => do
    let fc ← if lvl0 then rowFold0 l a (lb + S * q₀) S er else rowFoldE l a (lb + S * q₀) S er
    let d ← dotG a (min (2 ^ a) (t - q₀)) (lp + q₀) 1 (fc 0).n 1
    let rest ← foldsG lvl0 l lb S er lp t z (q₀ + 2 ^ a) as
    add d rest

/-- The column weight of a level over its positions `[q₀, t)` in chunks `as` (QA2's `colWeight`;
weights at `lp + q`, positions at the `K` cells `xb + q`, point at `ptb + k`, roots/inverses at the
`K` cells `rb + k`, `ib + k`, coordinate chunks `cs`, zero cells `z`, `zk`). -/
def colWG (cs : List Nat) (ptb ib rb lp xb t : Nat) (z : Cell) (zk : Nat) : Nat → List Nat → BM Cell
  | _, [] => pure z
  | q₀, a :: as => do
    let w ← colWeight a (min (2 ^ a) (t - q₀)) cs ptb ib rb (lp + q₀) (xb + q₀) z.n zk
    let rest ← colWG cs ptb ib rb lp xb t z zk (q₀ + 2 ^ a) as
    add w rest

/-- Contiguous `K` cells holding the constants `vs` (`const` rows from the `K` cell `g`). -/
def kconsts (g : Cell) : List FK → BM Unit
  | [] => pure ()
  | v :: vs => do
    let _ ← const .K v g
    kconsts g vs

/-- The roots of `subspaceRoots m`, then their inverses, as `K` constants (`2m` cells from the
pointer: roots at `+k`, inverses at `+m+k`). -/
def iwConsts (m : Nat) (g : Cell) : BM Unit := do
  kconsts g ((List.range m).map fun k => ((iwRoots m).getD k 0).c₀)
  kconsts g ((List.range m).map fun k => ((iwInvs m).getD k 0).c₀)

/-- The final weight `w + Σ_i λ_i W_i` (left to right, `F`'s `glued.foldl`). -/
def wsumG : Cell → List (Cell × Cell) → BM Cell
  | w, [] => pure w
  | w, (lam, W) :: gl => do
    let w' ← mulAdd .E lam W w
    wsumG w' gl

/-- `acc · Π_j (1 + a_j + b_j)` (the OOD weight `eq(z, x)`, `eqEval`, char 2) over the pairs `ab`
(`zc` a zero cell). -/
def eqZG (zc : Cell) : List (Cell × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | (a, b) :: ab, acc => do
    let s ← lin .E 1 1 a b
    let acc' ← mulAdd .E acc s zc
    eqZG zc ab acc'

/-- Copies of `cells` at consecutive `E` cells from the returned one. -/
def copiesG (cells : List Cell) : BM Nat := do
  let p ← getPtr
  let _ ← seqAll (cells.map copy)
  pure p.e

/-- The scalars at the lanes `ls` (`ldEW`) at consecutive `E` cells from the returned one. -/
def preloadG (ls : List Nat) : BM Nat := do
  let p ← getPtr
  let _ ← seqAll (ls.map ldEW)
  pure p.e

end Lvm.Har
