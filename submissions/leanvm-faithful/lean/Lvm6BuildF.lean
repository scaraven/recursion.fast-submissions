-- New for lvm6 (WP ST-5, STARTUP): a fast builder monad and its one bridge to `BM`. Additive: no existing
-- definition or statement changes.
import LvmVFastQ
import LvmE2QWKit

/-!
# A fast builder (`Lvm6.BF`, WP ST-5)

`BM α = Ptr → α × List Seg` computes, in every `bind`, the pointer after the first gadget from its segments
(`Ptr.adv`, two passes) and appends its segments (`++`, one copy). A segment is therefore traversed once per
enclosing `bind` in which it is on the left, and `mapB f (a :: as)` puts `mapB f as` on the left: the build is
quadratic in every `mapB` list and linear in the nesting depth.

* **`FM α = St → α × St`**: the state monad over `St` = the pointer, the blocks closed so far and the open glue
  run; `bind` is the state monad's, so a segment is pushed once (grouped on the spot, `out_pushAll`) and the
  pointer advanced by its own width.
* **`lift m`**: run a `BM` gadget and push its segments (one pass). **`mapBF`**: `mapB` as a loop.
* **`Rep mF m`** (`mF` *represents* `m`): `mF` from any state returns `m`'s output and the state with `m`'s
  segments pushed. **The bridge**: `rep_lift`, `rep_pure`, `rep_bind`, `rep_getPtr`, `rep_mapB` (the monad
  homomorphism, proved once) and `toProgramB_eq : Rep mF m → toProgramB nK nE mF = toProgramF nK nE m`.
  A fast twin is `m`'s text with `lift` at the leaves; its `Rep` follows from these lemmas (no gadget semantics
  is reproved).
* **`toProgramB`**: `toProgramF` on the state's blocks (no grouping pass).

Everything here is a loop or tail-recursive (the badge's stack is the default 8 MB).
-/

set_option autoImplicit false

namespace Lvm6.BF

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2

/-! ## The state and the monad -/

/-- `groupAuxN`'s step (`groupF` = `close` of the right fold of `gStep`). -/
def gStep : Seg → List Row × Nat × List Block → List Row × Nat × List Block
  | .row r, g =>
    if decide (glueCap ≤ g.2.1) then
      ([r], 1, if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2)
    else (r :: g.1, g.2.1 + 1, g.2.2)
  | .blk B, g => ([], 0, B :: (if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2))

/-- The blocks of a fold state: the open glue run (if any) first. -/
def close (g : List Row × Nat × List Block) : List Block := if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2

/-- **The glue blocks of a run of rows** given newest first (`groupF` of the run, by a left fold). -/
def flush (run : List Row) : List Block := close (run.foldl (fun g r ↦ gStep (.row r) g) ([], 0, []))

/-- The builder state: the allocation pointer, the blocks closed so far, and the current glue run (newest row
first). Segments are grouped as they are pushed (`groupF`'s blocks, no second pass). -/
structure St where
  /-- The next free cells. -/
  p : Ptr
  /-- The blocks before the current glue run. -/
  blks : Array Block
  /-- The current glue run's rows, newest first. -/
  run : List Row

/-- Push one segment: advance the pointer by its widths; a row joins the run, a block closes it. -/
@[inline] def St.push (s : St) (x : Seg) : St :=
  match x with
  | .row r => ⟨⟨s.p.k + x.w .K, s.p.e + x.w .E⟩, s.blks, r :: s.run⟩
  | .blk B => ⟨⟨s.p.k + x.w .K, s.p.e + x.w .E⟩, (s.blks ++ flush s.run).push B, []⟩

/-- The blocks of a state (the run closed). -/
def St.out (s : St) : List Block := s.blks.toList ++ flush s.run

/-- Push the segments in order (tail-recursive). -/
def pushAll : St → List Seg → St
  | s, [] => s
  | s, x :: xs => pushAll (s.push x) xs

/-- **The fast builder**: a state transformer over `St`. -/
def FM (α : Type) : Type := St → α × St

/-- The state monad's `bind`. -/
@[inline] def FM.bind {α β : Type} (m : FM α) (f : α → FM β) : FM β := fun s =>
  let r := m s
  f r.1 r.2

instance : Monad FM where
  pure x := fun s => (x, s)
  bind := FM.bind

/-- **A `BM` gadget in `FM`**: run it at the state's pointer and push its segments. -/
@[inline] def lift {α : Type} (m : BM α) : FM α := fun s =>
  let r := m s.p
  (r.1, pushAll s r.2)

/-- The current pointer. -/
@[inline] def getPtrF : FM Ptr := fun s => (s.p, s)

/-- `mapB` as a loop: `f` on every element in order, the outputs collected (reversed, then reversed back). -/
def mapBGo {α β : Type} (f : α → FM β) : List α → List β → St → List β × St
  | [], acc, s => (acc.reverse, s)
  | a :: as, acc, s =>
    let r := f a s
    mapBGo f as (r.1 :: acc) r.2

/-- **`mapB` in `FM`.** -/
@[inline] def mapBF {α β : Type} (f : α → FM β) (l : List α) : FM (List β) := mapBGo f l []

/-! ## Representation -/

/-- **`mF` represents `m`**: from every state, `m`'s output and the state with `m`'s segments pushed. -/
def Rep {α : Type} (mF : FM α) (m : BM α) : Prop :=
  ∀ s : St, mF s = ((m s.p).1, pushAll s (m s.p).2)

theorem pushAll_append : ∀ (s : St) (l₁ l₂ : List Seg), pushAll s (l₁ ++ l₂) = pushAll (pushAll s l₁) l₂
  | _, [], _ => rfl
  | s, x :: xs, l₂ => pushAll_append (s.push x) xs l₂

theorem pushAll_p : ∀ (s : St) (l : List Seg), (pushAll s l).p = s.p.adv l
  | s, [] => by simp [pushAll]
  | s, x :: xs => by
    rw [pushAll, pushAll_p (s.push x) xs, Ptr.adv_cons]
    cases x <;> rfl

theorem bind_def {α β : Type} (m : FM α) (f : α → FM β) (s : St) : (m >>= f) s = f (m s).1 (m s).2 := rfl

theorem pure_def {α : Type} (a : α) (s : St) : (pure a : FM α) s = (a, s) := rfl

/-! ## The homomorphism (proved once) -/

theorem rep_lift {α : Type} (m : BM α) : Rep (lift m) m := fun _ ↦ rfl

theorem rep_pure {α : Type} (a : α) : Rep (pure a : FM α) (pure a : BM α) := fun _ ↦ rfl

theorem rep_getPtr : Rep getPtrF getPtr := fun _ ↦ rfl

theorem rep_bind {α β : Type} {mF : FM α} {m : BM α} {fF : α → FM β} {f : α → BM β} (hm : Rep mF m)
    (hf : ∀ a, Rep (fF a) (f a)) : Rep (mF >>= fF) (m >>= f) := by
  intro s
  rw [bind_def, hm s, hf _ _, bind_apply, pushAll_p, pushAll_append]

theorem rep_mapBGo {α β : Type} {fF : α → FM β} {f : α → BM β} (hf : ∀ a, Rep (fF a) (f a)) :
    ∀ (l : List α) (acc : List β) (s : St),
      mapBGo fF l acc s = (acc.reverse ++ (mapB f l s.p).1, pushAll s (mapB f l s.p).2)
  | [], acc, s => by simp [mapBGo, mapB, pure_apply, pushAll]
  | a :: as, acc, s => by
    have e1 : mapBGo fF (a :: as) acc s = mapBGo fF as ((fF a s).1 :: acc) (fF a s).2 := rfl
    rw [e1, hf a s, rep_mapBGo hf as, pushAll_p]
    simp only [mapB, bind_apply, pure_apply, List.append_nil, pushAll_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem rep_mapB {α β : Type} {fF : α → FM β} {f : α → BM β} (hf : ∀ a, Rep (fF a) (f a)) (l : List α) :
    Rep (mapBF fF l) (mapB f l) := by
  intro s
  rw [mapBF, rep_mapBGo hf]
  simp

/-- `Rep` is closed under equal gadgets (to move along a definition's equation). -/
theorem Rep.of_eq {α : Type} {mF : FM α} {m m' : BM α} (h : Rep mF m) (e : m = m') : Rep mF m' := e ▸ h

/-! ## `BM`'s monad laws (function equalities) -/

theorem bm_bind_assoc {α β γ : Type} (m : BM α) (f : α → BM β) (g : β → BM γ) :
    (m >>= f) >>= g = m >>= fun x ↦ f x >>= g := by
  funext p
  simp only [bind_apply, List.append_assoc, Ptr.adv_append]

theorem bm_pure_bind {α β : Type} (a : α) (f : α → BM β) : ((pure a : BM α) >>= f) = f a := by
  funext p
  simp only [bind_apply, pure_apply, Ptr.adv_nil, List.nil_append]

theorem bm_bind_pure {α : Type} (m : BM α) : (m >>= fun x ↦ (pure x : BM α)) = m := by
  funext p
  simp only [bind_apply, pure_apply, List.append_nil]

theorem bm_bind_pure_unit (m : BM Unit) : (m >>= fun _ ↦ (pure () : BM Unit)) = m := by
  funext p
  simp only [bind_apply, pure_apply, List.append_nil]

/-! ## Left-recursive loops (`L (n + 1) = L n >>= …`) as forward loops -/

/-- `step i, …, step (i + k − 1)`, right-nested. -/
def stepsR (step : ℕ → BM Unit) (i : ℕ) : ℕ → BM Unit
  | 0 => pure ()
  | k + 1 => step i >>= fun _ ↦ stepsR step (i + 1) k

theorem stepsR_snoc (step : ℕ → BM Unit) : ∀ (k i : ℕ),
    (stepsR step i k >>= fun _ ↦ step (i + k)) = stepsR step i (k + 1)
  | 0, i => by simp only [stepsR, bm_pure_bind, Nat.add_zero, bm_bind_pure_unit]
  | k + 1, i => by
    rw [stepsR, bm_bind_assoc, show i + (k + 1) = i + 1 + k by omega]
    simp only [stepsR_snoc step k (i + 1)]
    rfl

/-- **A left-recursive `Unit` loop is the forward sequence of its steps.** -/
theorem leftU_eq {L : ℕ → BM Unit} {step : ℕ → BM Unit} (h0 : L 0 = pure ())
    (hs : ∀ n, L (n + 1) = L n >>= fun _ ↦ step n) : ∀ n, L n = stepsR step 0 n
  | 0 => h0
  | n + 1 => by rw [hs, leftU_eq h0 hs n, ← stepsR_snoc step n 0, Nat.zero_add]

/-- `k` steps from `i` as a loop. -/
def forUGo (step : ℕ → FM Unit) : ℕ → ℕ → St → Unit × St
  | 0, _, s => ((), s)
  | k + 1, i, s => forUGo step k (i + 1) (step i s).2

/-- **`step 0, …, step (n − 1)` in `FM`.** -/
@[inline] def forUF (step : ℕ → FM Unit) (n : ℕ) : FM Unit := forUGo step n 0

theorem rep_stepsR {step : ℕ → BM Unit} {stepF : ℕ → FM Unit} (hf : ∀ i, Rep (stepF i) (step i)) :
    ∀ (k i : ℕ), Rep (forUGo stepF k i) (stepsR step i k)
  | 0, _ => rep_pure ()
  | k + 1, i => rep_bind (hf i) fun _ ↦ rep_stepsR hf k (i + 1)

theorem rep_forU {L : ℕ → BM Unit} {step : ℕ → BM Unit} {stepF : ℕ → FM Unit} (h0 : L 0 = pure ())
    (hs : ∀ n, L (n + 1) = L n >>= fun _ ↦ step n) (hf : ∀ i, Rep (stepF i) (step i)) (n : ℕ) :
    Rep (forUF stepF n) (L n) := (rep_stepsR hf n 0).of_eq (leftU_eq h0 hs n).symm

theorem mapB_append {α β : Type} (f : α → BM β) : ∀ (l₁ l₂ : List α),
    mapB f (l₁ ++ l₂) = mapB f l₁ >>= fun a ↦ mapB f l₂ >>= fun b ↦ pure (a ++ b)
  | [], l₂ => by simp only [List.nil_append, mapB, bm_pure_bind, bm_bind_pure]
  | x :: xs, l₂ => by
    simp only [List.cons_append, mapB, mapB_append f xs l₂, bm_bind_assoc, bm_pure_bind]

/-- **A left-recursive accumulation (`ps ++ [p]`) is `mapB` over the range.** -/
theorem leftAcc_eq {β : Type} {L : ℕ → BM (List β)} {step : ℕ → BM β} (h0 : L 0 = pure [])
    (hs : ∀ n, L (n + 1) = L n >>= fun ps ↦ step n >>= fun p ↦ pure (ps ++ [p])) :
    ∀ n, L n = mapB step (List.range n)
  | 0 => h0
  | n + 1 => by
    rw [hs, leftAcc_eq h0 hs n, List.range_succ, mapB_append]
    simp only [mapB, bm_bind_assoc, bm_pure_bind]

theorem rep_leftAcc {β : Type} {L : ℕ → BM (List β)} {step : ℕ → BM β} {stepF : ℕ → FM β}
    (h0 : L 0 = pure []) (hs : ∀ n, L (n + 1) = L n >>= fun ps ↦ step n >>= fun p ↦ pure (ps ++ [p]))
    (hf : ∀ i, Rep (stepF i) (step i)) (n : ℕ) : Rep (mapBF stepF (List.range n)) (L n) :=
  (rep_mapB hf _).of_eq (leftAcc_eq h0 hs n).symm

/-! ## The program -/

theorem groupAuxN_foldr : ∀ δ : List Seg, Lvm.VF.groupAuxN δ = δ.foldr gStep ([], 0, [])
  | [] => rfl
  | .row r :: δ => by rw [Lvm.VF.groupAuxN, List.foldr_cons, ← groupAuxN_foldr δ]; rfl
  | .blk B :: δ => by rw [Lvm.VF.groupAuxN, List.foldr_cons, ← groupAuxN_foldr δ]; rfl

theorem groupF_foldr (δ : List Seg) : Lvm.VF.groupF δ = close (δ.foldr gStep ([], 0, [])) := by
  unfold Lvm.VF.groupF close
  rw [List.foldr_toArray, ← Lvm.VF.groupAuxN_foldr, groupAuxN_foldr]

theorem gStep_row_tail (r : Row) (g : List Row × Nat × List Block) (X : List Block) :
    gStep (.row r) (g.1, g.2.1, g.2.2 ++ X) =
      ((gStep (.row r) g).1, (gStep (.row r) g).2.1, (gStep (.row r) g).2.2 ++ X) := by
  obtain ⟨a, n, b⟩ := g
  simp only [gStep]
  split_ifs <;> simp

/-- Rows fold into the third component's front only: what lies behind it is carried. -/
theorem rows_foldr_tail (X : List Block) : ∀ rows : List Row,
    (rows.map Seg.row).foldr gStep ([], 0, X) =
      (((rows.map Seg.row).foldr gStep ([], 0, [])).1, ((rows.map Seg.row).foldr gStep ([], 0, [])).2.1,
        ((rows.map Seg.row).foldr gStep ([], 0, [])).2.2 ++ X)
  | [] => rfl
  | r :: rows => by
    simp only [List.map_cons, List.foldr_cons]
    rw [rows_foldr_tail X rows]
    exact gStep_row_tail _ _ _

theorem close_tail (g : List Row × Nat × List Block) (X : List Block) :
    close (g.1, g.2.1, g.2.2 ++ X) = close g ++ X := by
  unfold close
  split_ifs <;> simp

theorem flush_eq (run : List Row) : flush run = Lvm.VF.groupF (run.reverse.map Seg.row) := by
  rw [groupF_foldr, flush, List.foldr_map, List.foldr_reverse]

/-- **A block closes the run**: `groupF (rows ++ B :: δ) = groupF rows ++ B :: groupF δ`. -/
theorem groupF_rows_blk (rows : List Row) (B : Block) (δ : List Seg) :
    Lvm.VF.groupF (rows.map Seg.row ++ .blk B :: δ) =
      Lvm.VF.groupF (rows.map Seg.row) ++ B :: Lvm.VF.groupF δ := by
  rw [groupF_foldr, groupF_foldr, groupF_foldr, List.foldr_append, List.foldr_cons]
  have e : gStep (.blk B) (δ.foldr gStep ([], 0, [])) = ([], 0, B :: close (δ.foldr gStep ([], 0, []))) := rfl
  rw [e, rows_foldr_tail, close_tail]

/-- **Grouping as you push**: the state's blocks after pushing `δ` are its blocks before with the run and
`δ` grouped. -/
theorem out_pushAll : ∀ (δ : List Seg) (s : St),
    (pushAll s δ).out = s.blks.toList ++ Lvm.VF.groupF (s.run.reverse.map Seg.row ++ δ)
  | [], s => by simp [pushAll, St.out, flush_eq]
  | .row r :: δ, s => by
    rw [pushAll, out_pushAll δ]
    simp [St.push, List.reverse_cons, List.map_append, List.append_assoc]
  | .blk B :: δ, s => by
    rw [pushAll, out_pushAll δ, groupF_rows_blk]
    simp [St.push, flush_eq, List.append_assoc]

/-- **`toProgramF` on a fast gadget.** -/
def toProgramB {α : Type} (nInK nInE : Nat) (m : FM α) : Program :=
  let bs := (m ⟨⟨nInK, nInE⟩, #[], []⟩).2.out
  ⟨nInK, nInE, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

/-- **The bridge**: a fast gadget representing `m` builds `m`'s program. -/
theorem toProgramB_eq {α : Type} {mF : FM α} {m : BM α} (h : Rep mF m) (nInK nInE : Nat) :
    toProgramB nInK nInE mF = Lvm.VF.toProgramF nInK nInE m := by
  unfold toProgramB Lvm.VF.toProgramF
  rw [h, out_pushAll]
  simp

end Lvm6.BF
