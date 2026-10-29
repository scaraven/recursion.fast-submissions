-- New for `flock-recursive` (BLUEPRINT A.11 `walkAB`, §4.4 "The walk", revision 3.15; stage S-E9
-- wrote a first version, parked; stage S-E10 rewrote it over the row-emitting DAG; track L-circ).
import FRVIRTplDag

/-!
# `tplWalkAB_ok`: the DAG template computes the walk

BLUEPRINT A.11 (revision 3.15): the template `tplWalkG` (`FRVIRTplDag`) emits the BLAKE2s gadget
DAG — XOR rows, the product rows as two running sums. **`tplWalkAB_ok`**: if its gate equations
hold at wires whose inputs are `rowW′ ++ colW`, its two outputs are `Eval.walkImpl rowW′ colW`.

The proof is a **relational simulation** (`RelT`) between the row-emitting program and the walk
interpretation (`walkOps`) of `FRBlake2sGeneric`'s gadget program, statement for statement: a
template form denotes the walk value at the wires (`l.ev e = x`), the two running sums denote the
walk's accumulators, and the gate positions agree. A gate the program emits is a gate of the final
template (the program only appends: `DGrows`), so its equation holds at the wires (`emit_eqn`).
No closed term expands a form: every row has the few cells of one gadget step.
-/

namespace FR
namespace Tpl
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## Runs -/

theorem drun_bind {β γ : Type} (x : DB β) (f : β → DB γ) (s : DSt) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem drun_pure {β : Type} (b : β) (s : DSt) : (pure b : DB β).run s = (b, s) := rfl

theorem grun_bind {S β γ : Type} (x : GB S β) (f : β → GB S γ) (s : GState S) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem grun_pure {S β : Type} (b : β) (s : GState S) : (pure b : GB S β).run s = (b, s) := rfl

theorem le_alignUp (x b : ℕ) : x ≤ Circ.alignUp x b := by
  unfold Circ.alignUp
  have h := Nat.div_add_mod (x + 2 ^ b - 1) (2 ^ b)
  have h2 := Nat.mod_lt (x + 2 ^ b - 1) (Nat.two_pow_pos b)
  have h3 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [Nat.mul_comm] at h
  omega

/-- A vector from its own entries (stated for a variable, so that no closed vector is unfolded). -/
theorem ofFn_getFin {α : Type} {n : ℕ} (xs : Vector α n) : Vector.ofFn (fun i : Fin n => xs[i]) = xs :=
  Vector.ofFn_getElem

/-! ## Growth -/

/-- The program only appends gates. -/
def DGrows {γ : Type} (mt : DB γ) : Prop := ∀ s, s.gs.toList <+: (mt.run s).2.gs.toList

theorem dg_pure {γ : Type} (c : γ) : DGrows (pure c : DB γ) := fun _ => List.prefix_refl _

theorem dg_bind {β γ : Type} {x : DB β} {f : β → DB γ} (hx : DGrows x) (hf : ∀ b, DGrows (f b)) :
    DGrows (x >>= f) := fun s => (hx s).trans (hf _ _)

theorem dg_map {β γ : Type} {x : DB β} (f : β → γ) (hx : DGrows x) : DGrows (f <$> x) := hx

theorem dg_emit (g : Gate) : DGrows (emit g) := fun s => by
  show s.gs.toList <+: (s.gs.push g).toList
  rw [Array.toList_push]; exact List.prefix_append _ _

theorem dg_padTo (b : ℕ) : DGrows (padTo b) := fun s => by
  show s.gs.toList <+: (s.gs.push _).toList
  rw [Array.toList_push]; exact List.prefix_append _ _

theorem dg_cell (l : LinT) : DGrows (dcell l) := by
  unfold dcell; split
  · exact dg_pure _
  · exact dg_emit _

theorem dg_copy (l : LinT) : DGrows (dcopy l) := dg_emit _

section
variable (ri ci : ℕ → LinT)

theorem dg_get : DGrows (get : DB DSt) := fun _ => List.prefix_refl _

theorem dg_mul (a b : LinT) : DGrows (dmul ri ci a b) := fun s => by
  show s.gs.toList <+: ((s.gs.push _).push _).toList
  rw [Array.toList_push, Array.toList_push, List.append_assoc]; exact List.prefix_append _ _

theorem dg_vec {β : Type} : ∀ (n : ℕ) (f : Fin n → DB β), (∀ i, DGrows (f i)) → DGrows (dvec n f)
  | 0, _, _ => dg_pure _
  | n + 1, f, h => by
    unfold dvec
    exact dg_bind (dg_vec n _ fun i => h _) fun _ => dg_bind (h _) fun _ => dg_pure _

theorem dg_cellW (x : Vector LinT 32) : DGrows (dcellW x) := dg_vec _ _ fun _ => dg_cell _

theorem dg_addCarries (x y : Vector LinT 32) : ∀ n c, DGrows (daddCarries ri ci x y n c)
  | 0, _ => dg_pure _
  | n + 1, c => by
    unfold daddCarries
    exact dg_bind (dg_mul ri ci _ _) fun _ => dg_bind (dg_cell _) fun _ =>
      dg_bind (dg_addCarries x y n _) fun _ => dg_pure _

theorem dg_sumW (p q : Vector LinT 32) (cs : List LinT) : DGrows (dsumW p q cs) :=
  dg_vec _ _ fun _ => dg_cell _

theorem dg_addW (x y : Vector LinT 32) : DGrows (daddW ri ci x y) :=
  dg_bind (dg_addCarries ri ci x y 31 []) fun _ => dg_sumW _ _ _

theorem dg_majorities (x y z : Vector LinT 32) : ∀ n, DGrows (dmajorities ri ci x y z n)
  | 0 => dg_pure _
  | n + 1 => by
    unfold dmajorities
    exact dg_bind (dg_mul ri ci _ _) fun _ => dg_bind (dg_majorities x y z n) fun _ => dg_pure _

theorem dg_rippleCarries (p q : Vector LinT 32) : ∀ n c, DGrows (drippleCarries ri ci p q n c)
  | 0, _ => dg_pure _
  | n + 1, c => by
    unfold drippleCarries
    dsimp only
    split
    · exact dg_bind (dg_mul ri ci _ _) fun _ => dg_bind (dg_cell _) fun _ =>
        dg_bind (dg_rippleCarries p q n _) fun _ => dg_pure _
    · exact dg_bind (dg_rippleCarries p q n _) fun _ => dg_pure _

theorem dg_add3W (x y z : Vector LinT 32) : DGrows (dadd3W ri ci x y z) :=
  dg_bind (dg_majorities ri ci x y z 31) fun _ => dg_bind (dg_rippleCarries ri ci _ _ 31 []) fun _ =>
    dg_sumW _ _ _

theorem dg_gW (v : Vector (Vector LinT 32) 16) (a b c d : Fin 16) (mx my : Vector LinT 32) :
    DGrows (dgW ri ci v a b c d mx my) := by
  unfold dgW
  exact dg_bind (dg_padTo _) fun _ => dg_bind (dg_add3W ri ci _ _ _) fun _ =>
    dg_bind (dg_addW ri ci _ _) fun _ => dg_bind (dg_add3W ri ci _ _ _) fun _ =>
    dg_bind (dg_cellW _) fun _ => dg_bind (dg_addW ri ci _ _) fun _ =>
    dg_bind (dg_cellW _) fun _ => dg_pure _

theorem dg_roundW (v m' : Vector (Vector LinT 32) 16) (s : Vector (Fin 16) 16) :
    DGrows (droundW ri ci v m' s) := by
  unfold droundW
  exact dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ =>
    dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ =>
    dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ =>
    dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => dg_gW ri ci _ _ _ _ _ _ _

theorem dg_rounds (msg : Vector (Vector LinT 32) 16) :
    ∀ (l : List (Vector (Fin 16) 16)) v, DGrows (l.foldlM (fun v s => droundW ri ci v msg s) v)
  | [], _ => dg_pure _
  | s :: l, v => by
    rw [List.foldlM_cons]
    exact dg_bind (dg_roundW ri ci _ _ _) fun _ => dg_rounds msg l _

theorem dg_initW : DGrows (dvec 16 (dinitWord ci)) := by
  refine dg_vec _ _ fun w => ?_
  unfold dinitWord
  split
  · exact dg_pure _
  · split
    · exact dg_vec _ _ fun _ => dg_copy _
    · exact dg_vec _ _ fun _ => dg_copy _

theorem dg_compressW : DGrows (dcompressW ri ci) := by
  unfold dcompressW
  exact dg_bind (dg_initW ci) fun _ => dg_bind (dg_rounds ri ci _ _ _) fun _ =>
    dg_bind (dg_padTo _) fun _ => dg_vec _ _ fun _ => dg_cellW _

theorem dg_acc (b : Bool) (k : ℕ) (a : LinT) : DGrows (dacc ri b k a) := fun s => by
  show s.gs.toList <+: (s.gs.push _).toList
  rw [Array.toList_push]; exact List.prefix_append _ _

theorem dg_forM {β : Type} (f : β → DB Unit) (hf : ∀ b, DGrows (f b)) :
    ∀ l : List β, DGrows (l.forM f)
  | [] => dg_pure _
  | b :: l => dg_bind (hf b) fun _ => dg_forM f hf l

end

/-! ## The relation -/

section Rel
variable (e : Env) (G : List Gate)

/-- A walk state and a builder state agree: gate position, the locals count, the accumulators. -/
def DR (g : GState (F × F)) (s : DSt) : Prop :=
  g.next = s.next ∧ s.nl = nlocs s.gs.toList ∧ g.acc.1 = s.accA.ev e ∧ g.acc.2 = s.accB.ev e

/-- **The relational simulation**: from agreeing states, if the program's gates so far are a
prefix of `G`, the states agree after, and the results are related by `R`. -/
def RelT {β γ : Type} (mw : GB (F × F) β) (mt : DB γ) (R : β → γ → Prop) : Prop :=
  ∀ g s, DR e g s → (mt.run s).2.gs.toList <+: G →
    DR e (mw.run g).2 (mt.run s).2 ∧ R (mw.run g).1 (mt.run s).1

/-- A form denotes a value. -/
def VE (x : F) (l : LinT) : Prop := l.ev e = x

/-- A word of forms denotes a word of values. -/
def WE (x : Vector F 32) (y : Vector LinT 32) : Prop := ∀ i : Fin 32, y[i].ev e = x[i]

variable {e G}

theorem relT_pure {β γ : Type} {b : β} {c : γ} {R : β → γ → Prop} (h : R b c) :
    RelT e G (pure b) (pure c) R := fun _ _ hs _ => ⟨hs, h⟩

theorem relT_bind {β γ β' γ' : Type} {mw : GB (F × F) β} {mt : DB γ} {R : β → γ → Prop}
    {f : β → GB (F × F) β'} {h : γ → DB γ'} {Q : β' → γ' → Prop} (hm : RelT e G mw mt R)
    (hg : ∀ c, DGrows (h c)) (hf : ∀ b c, R b c → RelT e G (f b) (h c) Q) :
    RelT e G (mw >>= f) (mt >>= h) Q := by
  intro g s hs hp
  rw [drun_bind] at hp ⊢
  rw [grun_bind]
  obtain ⟨hs1, hr1⟩ := hm g s hs ((hg _ _).trans hp)
  exact hf _ _ hr1 _ _ hs1 hp

/-- A template-only step (the walk side is pure). -/
theorem relT_bindT {β γ β' γ' : Type} {b : β} {mt : DB γ} {R : β → γ → Prop} {mw : GB (F × F) β'}
    {h : γ → DB γ'} {Q : β' → γ' → Prop} (hm : RelT e G (pure b) mt R) (hg : ∀ c, DGrows (h c))
    (hf : ∀ c, R b c → RelT e G mw (h c) Q) : RelT e G mw (mt >>= h) Q := by
  intro g s hs hp
  rw [drun_bind] at hp ⊢
  obtain ⟨hs1, hr1⟩ := hm g s hs ((hg _ _).trans hp)
  exact hf _ hr1 _ _ hs1 hp

theorem relT_map {β γ β' γ' : Type} {mw : GB (F × F) β} {mt : DB γ} {R : β → γ → Prop}
    {f : β → β'} {h : γ → γ'} {Q : β' → γ' → Prop} (hm : RelT e G mw mt R)
    (hf : ∀ b c, R b c → Q (f b) (h c)) : RelT e G (f <$> mw) (h <$> mt) Q := fun g s hs hp => by
  obtain ⟨hs1, hr1⟩ := hm g s hs hp
  exact ⟨hs1, hf _ _ hr1⟩

/-- **An emitted gate's equation holds** (it is a gate of `G`). -/
theorem emit_eqn (hE : Eqns e G 0) {s : DSt} {g : Gate} (hn : s.nl = nlocs s.gs.toList)
    (hp : (s.gs.push g).toList <+: G) : g.Eqn e s.nl := by
  obtain ⟨t, ht⟩ := hp
  rw [Array.toList_push, List.append_assoc] at ht
  refine hE (s.nl, g) ?_
  rw [← ht, gatesAt_append, hn]
  simp [gatesAt]

theorem relT_emit (hE : Eqns e G 0) (g : Gate) {x : F}
    (hx : ∀ s : DSt, g.Eqn e s.nl → e.loc s.nl = x) :
    RelT e G (pure x) (emit g) (VE e) := fun gw s hs hp => by
  refine ⟨⟨hs.1, ?_, hs.2.2⟩, ?_⟩
  · show s.nl + g.nloc = nlocs (s.gs.push g).toList
    rw [Array.toList_push, hs.2.1]; simp [nlocs]
  · show (L s.nl).ev e = x
    rw [ev_L]; exact hx s (emit_eqn hE hs.2.1 hp)

theorem relT_cell (hE : Eqns e G 0) {l : LinT} {x : F} (h : l.ev e = x) :
    RelT e G (pure x) (dcell l) (VE e) := by
  unfold dcell; split
  · exact relT_pure h
  · exact relT_emit hE _ fun s hg => by simp only [Gate.Eqn] at hg; rw [hg]; simp [h]

theorem relT_copy (hE : Eqns e G 0) {l : LinT} {x : F} (h : l.ev e = x) :
    RelT e G (pure x) (dcopy l) (VE e) :=
  relT_emit hE _ fun s hg => by simp only [Gate.Eqn] at hg; rw [hg]; simp [h]

theorem relT_padTo (b : ℕ) : RelT e G (pure ()) (padTo b) (fun _ _ => True) := fun g s hs _ => by
  refine ⟨⟨hs.1, ?_, hs.2.2⟩, trivial⟩
  show Circ.alignUp s.nl b = nlocs (s.gs.push _).toList
  rw [Array.toList_push]
  simp only [nlocs, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Gate.nloc]
  rw [← nlocs, ← hs.2.1]
  have := le_alignUp s.nl b
  omega

theorem relT_vec {β γ : Type} {R : β → γ → Prop} :
    ∀ (n : ℕ) (f : Fin n → β) (t : Fin n → DB γ), (∀ i, RelT e G (pure (f i)) (t i) R) →
      (∀ i, DGrows (t i)) → RelT e G (pure (Vector.ofFn f)) (dvec n t) (fun x y => ∀ i : Fin n, R x[i] y[i])
  | 0, _, _, _, _ => relT_pure fun i => i.elim0
  | n + 1, f, t, h, hg => by
    unfold dvec
    refine relT_bindT (relT_vec n (fun i => f i.castSucc) _ (fun i => h _) (fun i => hg _))
      (fun _ => dg_bind (hg _) fun _ => dg_pure _) fun v hv => ?_
    refine relT_bindT (h (Fin.last n)) (fun _ => dg_pure _) fun x hx => relT_pure fun i => ?_
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.coe_castSucc, Vector.getElem_push,
        j.isLt, ↓reduceDIte] at hv ⊢
      exact hv j
    · simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.val_last, Vector.getElem_push_eq]
      exact hx

end Rel

/-! ## The gadgets -/

theorem eqns_mem {e : Env} {G : List Gate} (hE : Eqns e G 0) {L₀ t : List Gate}
    (h : L₀ ++ t <+: G) : Eqns e t (nlocs L₀) := fun p hp => by
  obtain ⟨u, hu⟩ := h
  refine hE p ?_
  rw [← hu, gatesAt_append, gatesAt_append, zero_add]
  exact List.mem_append_left _ (List.mem_append_right _ hp)

section Gad
variable {e : Env} {G : List Gate} (hE : Eqns e G 0) {ri ci : ℕ → LinT}
  {ew wt : Pos Blake2sCircuit.m → F}
  (hri : ∀ k : Pos Blake2sCircuit.m, (ri k.val).ev e = ew k)
  (hci : ∀ k : Pos Blake2sCircuit.m, (ci k.val).ev e = wt k)
include hE hri hci

theorem relT_mul {a b : F} {a' b' : LinT} (ha : a'.ev e = a) (hb : b'.ev e = b) :
    RelT e G ((walkOps ew wt).mul a b) (dmul ri ci a' b') (VE e) := fun g s hs hp => by
  have hp' : s.gs.toList ++ [Gate.mulAdd (ri (pos (m := Blake2sCircuit.m) s.next).val) a' s.accA,
      Gate.mulAdd (ri (pos (m := Blake2sCircuit.m) s.next).val) b' s.accB] <+: G := by
    have : ((s.gs.push (Gate.mulAdd (ri (pos (m := Blake2sCircuit.m) s.next).val) a' s.accA)).push
        (Gate.mulAdd (ri (pos (m := Blake2sCircuit.m) s.next).val) b' s.accB)).toList <+: G := hp
    simpa [Array.toList_push] using this
  have h2 := eqns_mem hE hp'
  simp only [Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h2
  rw [← hs.2.1] at h2
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show g.next + 1 = s.next + 1; rw [hs.1]
  · show s.nl + 2 = nlocs ((s.gs.push _).push _).toList
    simp [Array.toList_push, nlocs, hs.2.1, Gate.nloc]
  · show g.acc.1 + ew (pos g.next) * a = (L s.nl).ev e
    rw [ev_L, h2a, hri, hs.1, ha, hs.2.2.1]; ring
  · show g.acc.2 + ew (pos g.next) * b = (L (s.nl + 1)).ev e
    rw [ev_L, h2b, hri, hs.1, hb, hs.2.2.2]; ring
  · show (ci (pos (m := Blake2sCircuit.m) s.next).val).ev e = wt (pos g.next)
    rw [hci, hs.1]

omit hri hci in
theorem relT_cellW {x : Vector F 32} {x' : Vector LinT 32} (h : WE e x x') :
    RelT e G (pure x) (dcellW x') (WE e) := by
  have := relT_vec (e := e) (G := G) (R := VE e) 32 (fun i => x[i]) (fun i => dcell x'[i])
    (fun i => relT_cell hE (h i)) (fun _ => dg_cell _)
  rw [ofFn_getFin] at this
  exact this

omit hE hri in
theorem we_inW (b : ℕ) : WE e ((walkOps ew wt).inW b) (dinW ci b) := fun i => by
  simp only [GOps.inW, dinW, dvar, Fin.getElem_fin, Vector.getElem_ofFn, walkOps, hci]

omit hE hri in
theorem we_litW (c : UInt32) : WE e ((walkOps ew wt).litW constPos c) (dlitW ci c) := fun i => by
  simp only [GOps.litW, dlitW, dvar, Fin.getElem_fin, Vector.getElem_ofFn, walkOps]
  split_ifs <;> simp [hci]

omit hE hri hci in
theorem we_xorW {x y : Vector F 32} {x' y' : Vector LinT 32} (hx : WE e x x') (hy : WE e y y') :
    WE e ((walkOps ew wt).xorW x y) (dxorW x' y') := fun i => by
  simp only [GOps.xorW, dxorW, dx, Fin.getElem_fin, Vector.getElem_ofFn, walkOps, ev_append]
  rw [← Fin.getElem_fin, hx i, ← Fin.getElem_fin, hy i]; rfl

omit hE hri hci in
theorem we_rotrW {x : Vector F 32} {x' : Vector LinT 32} (hx : WE e x x') (n : ℕ) :
    WE e (GOps.rotrW x n) (GOps.rotrW x' n) := fun i => by
  simp only [GOps.rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact hx ⟨_, Nat.mod_lt _ (by decide)⟩

omit hE hri hci in
theorem we_xor3W {x y z : Vector F 32} {x' y' z' : Vector LinT 32} (hx : WE e x x') (hy : WE e y y')
    (hz : WE e z z') : WE e ((walkOps ew wt).xor3W x y z) (dxor3W x' y' z') := fun i => by
  simp only [GOps.xor3W, dxor3W, dx, Fin.getElem_fin, Vector.getElem_ofFn, walkOps, ev_append]
  rw [← Fin.getElem_fin, hx i, ← Fin.getElem_fin, hy i, ← Fin.getElem_fin, hz i]; rfl

omit hE hri hci in
theorem getD_f2 {l : List F} {l' : List LinT} (h : List.Forall₂ (VE e) l l') :
    ∀ i, (l'.getD i []).ev e = l.getD i 0 := by
  induction h with
  | nil => intro i; simp
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => exact hab
    | succ i => simpa using ih i

omit hE hri hci in
theorem ev_dx {a b : F} {a' b' : LinT} (ha : a'.ev e = a) (hb : b'.ev e = b) :
    (dx a' b').ev e = (walkOps ew wt).xor a b := by
  simp only [dx, ev_append, ha, hb]; rfl

omit hE hri hci in
theorem we_shiftW {ms : List F} {ms' : List LinT} (h : List.Forall₂ (VE e) ms ms') :
    WE e ((walkOps ew wt).shiftW ms) (dshiftW ms') := fun i => by
  simp only [GOps.shiftW, dshiftW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · simp [walkOps]
  · rw [getD_f2 h]; rfl

omit hri hci in
theorem relT_sumW {p q : Vector F 32} {p' q' : Vector LinT 32} {cs : List F} {cs' : List LinT}
    (hp : WE e p p') (hq : WE e q q') (hc : List.Forall₂ (VE e) cs cs') :
    RelT e G (pure ((walkOps ew wt).sumW p q cs)) (dsumW p' q' cs') (WE e) := by
  have := relT_vec (e := e) (G := G) (R := VE e) 32
    (fun i => (walkOps ew wt).xor ((walkOps ew wt).xor p[i] q[i]) (cs.getD i (walkOps ew wt).zero))
    (fun i => dcell (dx (dx p'[i] q'[i]) (cs'.getD i [])))
    (fun i => relT_cell hE (ev_dx (ev_dx (hp i) (hq i)) (getD_f2 hc i))) (fun _ => dg_cell _)
  exact this

theorem relT_addCarries {x y : Vector F 32} {x' y' : Vector LinT 32} (hx : WE e x x') (hy : WE e y y') :
    ∀ (n : ℕ) {c : F} {c' : LinT}, c'.ev e = c →
      RelT e G ((walkOps ew wt).addCarries x y n c) (daddCarries ri ci x' y' n c')
        (List.Forall₂ (VE e))
  | 0, c, c', hc => relT_pure (List.Forall₂.cons hc .nil)
  | n + 1, c, c', hc => by
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi
    simp only [GOps.addCarries, daddCarries]
    refine relT_bind (relT_mul hE hri hci (ev_dx hxi hc) (ev_dx hyi hc))
      (fun _ => dg_bind (dg_cell _) fun _ => dg_bind (dg_addCarries ri ci _ _ _ _) fun _ => dg_pure _)
      fun g g' hg => ?_
    refine relT_bindT (b := (walkOps ew wt).xor c g) (relT_cell hE (ev_dx hc hg))
      (fun _ => dg_bind (dg_addCarries ri ci _ _ _ _) fun _ => dg_pure _) fun c'' hc'' => ?_
    exact relT_bind (relT_addCarries hx hy n hc'') (fun _ => dg_pure _) fun r r' hr =>
      relT_pure (List.Forall₂.cons hc hr)

omit hE hri hci in
theorem relT_mapBind {β γ β' γ' : Type} {mw : GB (F × F) β} {mt : DB γ} {R : β → γ → Prop}
    {f : β → β'} {h : γ → DB γ'} {Q : β' → γ' → Prop} (hm : RelT e G mw mt R)
    (hg : ∀ c, DGrows (h c)) (hf : ∀ b c, R b c → RelT e G (pure (f b)) (h c) Q) :
    RelT e G (f <$> mw) (mt >>= h) Q := by
  intro g s hs hp
  rw [drun_bind] at hp ⊢
  obtain ⟨hs1, hr1⟩ := hm g s hs ((hg _ _).trans hp)
  exact hf _ _ hr1 _ _ hs1 hp

theorem relT_addW {x y : Vector F 32} {x' y' : Vector LinT 32} (hx : WE e x x') (hy : WE e y y') :
    RelT e G ((walkOps ew wt).addW x y) (daddW ri ci x' y') (WE e) :=
  relT_mapBind (relT_addCarries hE hri hci hx hy 31 (by simp [walkOps]))
    (fun _ => dg_sumW _ _ _) fun _ _ hc => relT_sumW hE hx hy hc

theorem relT_majorities {x y z : Vector F 32} {x' y' z' : Vector LinT 32} (hx : WE e x x')
    (hy : WE e y y') (hz : WE e z z') : ∀ n : ℕ,
      RelT e G ((walkOps ew wt).majorities x y z n) (dmajorities ri ci x' y' z' n)
        (List.Forall₂ (VE e))
  | 0 => relT_pure .nil
  | n + 1 => by
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    have hzi := hz ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi hzi
    simp only [GOps.majorities, dmajorities]
    refine relT_bind (relT_mul hE hri hci (ev_dx hxi hzi) (ev_dx hyi hzi))
      (fun _ => dg_bind (dg_majorities ri ci _ _ _ _) fun _ => dg_pure _) fun g g' hg => ?_
    exact relT_bind (relT_majorities hx hy hz n) (fun _ => dg_pure _) fun r r' hr =>
      relT_pure (List.Forall₂.cons (ev_dx hg hzi) hr)

theorem relT_rippleCarries {p q : Vector F 32} {p' q' : Vector LinT 32} (hp : WE e p p')
    (hq : WE e q q') : ∀ (n : ℕ) {c : F} {c' : LinT}, c'.ev e = c →
      RelT e G ((walkOps ew wt).rippleCarries p q n c) (drippleCarries ri ci p' q' n c')
        (List.Forall₂ (VE e))
  | 0, c, c', hc => relT_pure (List.Forall₂.cons hc .nil)
  | n + 1, c, c', hc => by
    simp only [GOps.rippleCarries, drippleCarries]
    by_cases hi : 1 ≤ 30 - n
    · simp only [hi, ↓reduceIte]
      have hpi := hp ⟨30 - n, by omega⟩
      have hqi := hq ⟨30 - n, by omega⟩
      simp only [Fin.getElem_fin] at hpi hqi
      refine relT_bind (relT_mul hE hri hci (ev_dx hpi hc) (ev_dx hqi hc))
        (fun _ => dg_bind (dg_cell _) fun _ => dg_bind (dg_rippleCarries ri ci _ _ _ _) fun _ =>
          dg_pure _) fun g g' hg => ?_
      refine relT_bindT (b := (walkOps ew wt).xor c g) (relT_cell hE (ev_dx hc hg))
        (fun _ => dg_bind (dg_rippleCarries ri ci _ _ _ _) fun _ => dg_pure _) fun c'' hc'' => ?_
      exact relT_bind (relT_rippleCarries hp hq n hc'') (fun _ => dg_pure _) fun r r' hr =>
        relT_pure (List.Forall₂.cons hc hr)
    · simp only [hi, ↓reduceIte]
      exact relT_bind (relT_rippleCarries hp hq n hc) (fun _ => dg_pure _) fun r r' hr =>
        relT_pure (List.Forall₂.cons hc hr)

theorem relT_add3W {x y z : Vector F 32} {x' y' z' : Vector LinT 32} (hx : WE e x x')
    (hy : WE e y y') (hz : WE e z z') :
    RelT e G ((walkOps ew wt).add3W x y z) (dadd3W ri ci x' y' z') (WE e) := by
  unfold GOps.add3W dadd3W
  refine relT_bind (relT_majorities hE hri hci hx hy hz 31)
    (fun _ => dg_bind (dg_rippleCarries ri ci _ _ _ _) fun _ => dg_sumW _ _ _) fun ms ms' hms => ?_
  have h3 := we_xor3W (ew := ew) (wt := wt) hx hy hz
  have hs := we_shiftW (ew := ew) (wt := wt) hms
  exact relT_mapBind (relT_rippleCarries hE hri hci h3 hs 31 (by simp [walkOps]))
    (fun _ => dg_sumW _ _ _) fun _ _ hc => relT_sumW hE h3 hs hc

/-- A state of words of forms denotes a state of words. -/
def VW (e : Env) {k : ℕ} (v : Vector (Vector F 32) k) (v' : Vector (Vector LinT 32) k) : Prop :=
  ∀ j : Fin k, WE e v[j] v'[j]

omit hE hri hci in
theorem vw_set {k : ℕ} {v : Vector (Vector F 32) k} {v' : Vector (Vector LinT 32) k} (hv : VW e v v')
    (a : Fin k) {x : Vector F 32} {x' : Vector LinT 32} (hx : WE e x x') :
    VW e (v.set a x) (v'.set a x') := fun j => by
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · exact hx
  · exact hv j

theorem relT_gW {v : Vector (Vector F 32) 16} {v' : Vector (Vector LinT 32) 16} (hv : VW e v v')
    (a b c d : Fin 16) {mx my : Vector F 32} {mx' my' : Vector LinT 32} (hmx : WE e mx mx')
    (hmy : WE e my my') :
    RelT e G ((walkOps ew wt).gW v a b c d mx my) (dgW ri ci v' a b c d mx' my') (VW e) := by
  unfold GOps.gW dgW
  refine relT_bindT (b := ()) (relT_padTo _) (fun _ => ?_) fun _ _ => ?_
  · exact dg_bind (dg_add3W ri ci _ _ _) fun _ => dg_bind (dg_addW ri ci _ _) fun _ =>
      dg_bind (dg_add3W ri ci _ _ _) fun _ => dg_bind (dg_cellW _) fun _ =>
      dg_bind (dg_addW ri ci _ _) fun _ => dg_bind (dg_cellW _) fun _ => dg_pure _
  refine relT_bind (relT_add3W hE hri hci (hv a) (hv b) hmx) (fun _ => ?_) fun a1 a1' ha1 => ?_
  · exact dg_bind (dg_addW ri ci _ _) fun _ =>
      dg_bind (dg_add3W ri ci _ _ _) fun _ => dg_bind (dg_cellW _) fun _ =>
      dg_bind (dg_addW ri ci _ _) fun _ => dg_bind (dg_cellW _) fun _ => dg_pure _
  have hd1 := we_rotrW (we_xorW (ew := ew) (wt := wt) (hv d) ha1) 16
  refine relT_bind (relT_addW hE hri hci (hv c) hd1) (fun _ => ?_) fun c1 c1' hc1 => ?_
  · exact dg_bind (dg_add3W ri ci _ _ _) fun _ => dg_bind (dg_cellW _) fun _ =>
      dg_bind (dg_addW ri ci _ _) fun _ => dg_bind (dg_cellW _) fun _ => dg_pure _
  have hb1 := we_rotrW (we_xorW (ew := ew) (wt := wt) (hv b) hc1) 12
  refine relT_bind (relT_add3W hE hri hci ha1 hb1 hmy) (fun _ => ?_) fun a2 a2' ha2 => ?_
  · exact dg_bind (dg_cellW _) fun _ => dg_bind (dg_addW ri ci _ _) fun _ =>
      dg_bind (dg_cellW _) fun _ => dg_pure _
  refine relT_bindT (b := (walkOps ew wt).xorW (GOps.rotrW ((walkOps ew wt).xorW v[d] a1) 16) a2)
    (relT_cellW hE (we_xorW hd1 ha2)) (fun _ => ?_) fun t2 ht2 => ?_
  · exact dg_bind (dg_addW ri ci _ _) fun _ => dg_bind (dg_cellW _) fun _ => dg_pure _
  have hd2 := we_rotrW ht2 8
  refine relT_bind (relT_addW hE hri hci hc1 hd2) (fun _ => ?_) fun c2 c2' hc2 => ?_
  · exact dg_bind (dg_cellW _) fun _ => dg_pure _
  refine relT_bindT (b := (walkOps ew wt).xorW (GOps.rotrW ((walkOps ew wt).xorW v[b] c1) 12) c2)
    (relT_cellW hE (we_xorW hb1 hc2)) (fun _ => dg_pure _) fun t3 ht3 => ?_
  exact relT_pure (vw_set (vw_set (vw_set (vw_set hv a ha2) b (we_rotrW ht3 7)) c hc2) d hd2)

attribute [local irreducible] GOps.gW dgW

theorem relT_roundW {v m' : Vector (Vector F 32) 16} {v'' m'' : Vector (Vector LinT 32) 16}
    (s : Vector (Fin 16) 16) (hv : VW e v v'') (hm : VW e m' m'') :
    RelT e G ((walkOps ew wt).roundW v m' s) (droundW ri ci v'' m'' s) (VW e) := by
  unfold GOps.roundW droundW
  refine relT_bind (relT_gW hE hri hci hv 0 4 8 12 (hm _) (hm _)) (fun _ => ?_) fun v1 v1' h1 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h1 1 5 9 13 (hm _) (hm _)) (fun _ => ?_) fun v2 v2' h2 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h2 2 6 10 14 (hm _) (hm _)) (fun _ => ?_) fun v3 v3' h3 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h3 3 7 11 15 (hm _) (hm _)) (fun _ => ?_) fun v4 v4' h4 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h4 0 5 10 15 (hm _) (hm _)) (fun _ => ?_) fun v5 v5' h5 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h5 1 6 11 12 (hm _) (hm _)) (fun _ => ?_) fun v6 v6' h6 => ?_
  · repeat' (first | exact dg_gW ri ci _ _ _ _ _ _ _ | refine dg_bind (dg_gW ri ci _ _ _ _ _ _ _) fun _ => ?_)
  refine relT_bind (relT_gW hE hri hci h6 2 7 8 13 (hm _) (hm _)) (fun _ => ?_) fun v7 v7' h7 => ?_
  · exact dg_gW ri ci _ _ _ _ _ _ _
  exact relT_gW hE hri hci h7 3 4 9 14 (hm _) (hm _)

attribute [local irreducible] GOps.roundW droundW

theorem relT_rounds {msg : Vector (Vector F 32) 16} {msg' : Vector (Vector LinT 32) 16}
    (hm : VW e msg msg') : ∀ (l : List (Vector (Fin 16) 16)) {v v'}, VW e v v' →
      RelT e G (l.foldlM (fun v s => (walkOps ew wt).roundW v msg s) v)
        (l.foldlM (fun v s => droundW ri ci v msg' s) v') (VW e)
  | [], _, _, hv => relT_pure hv
  | s :: l, _, _, hv => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact relT_bind (relT_roundW hE hri hci s hv hm) (fun _ => dg_rounds ri ci _ _ _)
      fun _ _ hw => relT_rounds hm l hw

attribute [local irreducible] GOps.initW

theorem relT_initW : RelT e G (pure (walkOps ew wt).initW) (dvec 16 (dinitWord ci)) (VW e) := by
  have key := relT_vec (e := e) (G := G) (R := WE e) 16 (fun w => (walkOps ew wt).initW[w])
    (dinitWord ci) (fun w => ?_) (fun w => ?_)
  · rw [ofFn_getFin] at key
    exact key
  · have hw : (walkOps ew wt).initW[w] = if w.val < 8 then (walkOps ew wt).inW (32 * w) else
        if w.val < 12 then (walkOps ew wt).litW constPos iv[w.val - 8] else (walkOps ew wt).xorW
          ((walkOps ew wt).litW constPos iv[w.val - 8]) ((walkOps ew wt).inW
            (counterLo + 32 * (w.val - 12))) := by
      rw [GOps.initW, Fin.getElem_fin, Vector.getElem_ofFn]
    rw [hw]
    unfold dinitWord
    split_ifs with h1 h2
    · exact relT_pure (we_inW (ew := ew) hci _)
    · have := relT_vec (e := e) (G := G) (R := VE e) 32 (fun i => ((walkOps ew wt).litW constPos
        iv[w.val - 8])[i]) _ (fun i => relT_copy hE ((we_litW (ew := ew) hci _) i)) (fun _ => dg_copy _)
      rw [ofFn_getFin] at this
      exact this
    · have hx := we_xorW (ew := ew) (wt := wt) (we_litW (ew := ew) hci iv[w.val - 8])
        (we_inW (ew := ew) hci (counterLo + 32 * (w.val - 12)))
      have := relT_vec (e := e) (G := G) (R := VE e) 32 (fun i => ((walkOps ew wt).xorW
        ((walkOps ew wt).litW constPos iv[w.val - 8]) ((walkOps ew wt).inW
          (counterLo + 32 * (w.val - 12))))[i]) _ (fun i => relT_copy hE (hx i)) (fun _ => dg_copy _)
      rw [ofFn_getFin] at this
      exact this
  · unfold dinitWord
    split_ifs
    · exact dg_pure _
    · exact dg_vec _ _ fun _ => dg_copy _
    · exact dg_vec _ _ fun _ => dg_copy _


/-- The compression's output words. -/
def OW (e : Env) (r : Vector (Vector F 32) 8) (r' : Vector (Vector LinT 32) 8) : Prop :=
  ∀ w : Fin 8, WE e r[w] r'[w]

theorem relT_compressW : RelT e G (walkOps ew wt).compressW (dcompressW ri ci) (OW e) := by
  have hmsg : VW e (Vector.ofFn fun w : Fin 16 => (walkOps ew wt).inW (msgBase + 32 * w))
      (Vector.ofFn fun w : Fin 16 => dinW ci (msgBase + 32 * w)) := fun w => by
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]; exact we_inW (ew := ew) hci _
  unfold GOps.compressW dcompressW
  dsimp only
  rw [← Vector.foldlM_toList]
  refine relT_bindT (b := (walkOps ew wt).initW) (relT_initW hE hri hci) (fun _ => ?_)
    fun v0 hv0 => ?_
  · exact dg_bind (dg_rounds ri ci _ _ _) fun _ => dg_bind (dg_padTo _) fun _ =>
      dg_vec _ _ fun _ => dg_cellW _
  refine relT_bind (relT_rounds hE hri hci hmsg sigma.toList hv0) (fun _ => ?_) fun v v' hv => ?_
  · exact dg_bind (dg_padTo _) fun _ => dg_vec _ _ fun _ => dg_cellW _
  refine relT_bindT (b := ()) (relT_padTo _) (fun _ => dg_vec _ _ fun _ => dg_cellW _) fun _ _ => ?_
  have := relT_vec (e := e) (G := G) (R := WE e) 8
    (fun w : Fin 8 => (walkOps ew wt).xorW ((walkOps ew wt).xorW v[w] v[w.val + 8])
      ((walkOps ew wt).inW (32 * w))) (dfinWord ci v')
    (fun w => relT_cellW hE (we_xorW (we_xorW (hv ⟨w, by omega⟩) (hv ⟨w.val + 8, by omega⟩))
      (we_inW (ew := ew) hci (32 * w)))) (fun _ => dg_cellW _)
  exact this

end Gad

end Tpl
end FR

namespace FR
namespace Tpl
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## The accumulations and `tplWalkAB_ok` -/

/-- An accumulation's contribution to `A` (`b = false`) or `B` (`b = true`). -/
def accC (e : Env) (ri : ℕ → LinT) (b : Bool) (t : Bool × ℕ × LinT) : F :=
  if t.1 = b then (ri t.2.1).ev e * t.2.2.ev e else 0

theorem acc_forM {e : Env} {G : List Gate} (hE : Eqns e G 0) (ri : ℕ → LinT) :
    ∀ (l : List (Bool × ℕ × LinT)) (s : DSt), s.nl = nlocs s.gs.toList →
      ((l.forM fun t => dacc ri t.1 t.2.1 t.2.2).run s).2.gs.toList <+: G →
      ((l.forM fun t => dacc ri t.1 t.2.1 t.2.2).run s).2.accA.ev e =
          s.accA.ev e + (l.map (accC e ri false)).sum ∧
        ((l.forM fun t => dacc ri t.1 t.2.1 t.2.2).run s).2.accB.ev e =
          s.accB.ev e + (l.map (accC e ri true)).sum
  | [], s, _, _ => ⟨by simp; rfl, by simp; rfl⟩
  | t :: l, s, hn, hp => by
    obtain ⟨b, k, a⟩ := t
    have hp2 : ((l.forM fun t => dacc ri t.1 t.2.1 t.2.2).run ((dacc ri b k a).run s).2).2.gs.toList
        <+: G := hp
    have hp' : (s.gs.push (.mulAdd (ri k) a (if b then s.accB else s.accA))).toList <+: G :=
      (dg_forM (fun t => dacc ri t.1 t.2.1 t.2.2) (fun t => dg_acc ri _ _ _) l _).trans hp2
    have heq := emit_eqn hE hn hp'
    simp only [Gate.Eqn] at heq
    have hn' : s.nl + 1 = nlocs (s.gs.push (.mulAdd (ri k) a (if b then s.accB else s.accA))).toList := by
      rw [Array.toList_push, hn]; simp [nlocs, Gate.nloc]
    obtain ⟨ih1, ih2⟩ := acc_forM hE ri l _ hn' hp
    refine ⟨?_, ?_⟩
    · refine ih1.trans ?_
      cases b <;> simp [accC, ev_L, heq, List.map_cons, List.sum_cons] <;> ring
    · refine ih2.trans ?_
      cases b <;> simp [accC, ev_L, heq, List.map_cons, List.sum_cons] <;> ring

theorem sum_flatMap' {α β : Type} (l : List α) (f : α → List β) (g : β → F) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem foldl_upd (ew wt : Pos Blake2sCircuit.m → F) (c : F) (L : List (Pos Blake2sCircuit.m × F))
    (s : F × F) : L.foldl (fun s p => (walkOps ew wt).upd s p.1 p.2 c) s =
      (s.1 + (L.map fun p => ew p.1 * p.2).sum, s.2 + (L.map fun p => ew p.1 * c).sum) := by
  induction L generalizing s with
  | nil => simp
  | cons p L ih => rw [List.foldl_cons, ih]; simp [walkOps, add_assoc]

variable {e : Env}

section Vals
variable {rw cw : Array F} (hi : InpIs e (rw.toList ++ cw.toList))
include hi

theorem rowI_ev (k : ℕ) : (rowI rw.size k).ev e = rw.getD k 0 := by
  by_cases h : k < rw.size
  · simp only [rowI, h, ↓reduceIte]
    rw [ev_I, hi, getD_append_left (by simpa using h), arr_getD]
  · simp [rowI, h, Array.getD]

theorem colI_ev (j : ℕ) : (colI rw.size cw.size j).ev e = cw.getD j 0 := by
  by_cases h : j < cw.size
  · simp only [colI, h, ↓reduceIte]
    rw [ev_I, hi, ← Array.length_toList, getD_append_right, arr_getD]
  · simp [colI, h, Array.getD]

end Vals

attribute [local irreducible] dcompressW

theorem sum_zero_map (l : List ℕ) : (l.map fun _ => (0 : F)).sum = 0 := by
  induction l <;> simp [*]

theorem outPairs_ev {e : Env} {r : Vector (Vector F 32) 8} {r' : Vector (Vector LinT 32) 8}
    (h : OW e r r') : (outPairs r').map (fun p => (p.1, p.2.ev e)) = outPairs r := by
  simp only [outPairs, List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun w _ => List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  have := h w i
  simpa only [Fin.getElem_fin] using this

/-- **`walkAB`'s DAG template computes `implC`'s walk** (`Eval.walkImpl`): the gate equations at
wires whose inputs are `rowW′ ++ colW` give the two outputs `walkImpl rowW′ colW`. -/
theorem tplWalkAB_ok {rw cw : Array F} (hi : InpIs e (rw.toList ++ cw.toList))
    (h : Eqns e (tplWalkG rw.size cw.size).gates 0) :
    (tplWalkG rw.size cw.size).outs.map (LinT.ev e) =
      Circ.encV (.f (Eval.walkImpl rw cw).1) ++ Circ.encV (.f (Eval.walkImpl rw cw).2) := by
  have hri : ∀ k : Pos Blake2sCircuit.m, (rowI rw.size k.val).ev e = Eval.onPos rw k :=
    fun k => rowI_ev hi _
  have hci : ∀ k : Pos Blake2sCircuit.m, (colI rw.size cw.size k.val).ev e = Eval.onPos cw k :=
    fun k => colI_ev hi _
  have hpk : ∀ k < 2 ^ Blake2sCircuit.m, (pos (m := Blake2sCircuit.m) k).val = k := fun k hk =>
    Nat.mod_eq_of_lt hk
  unfold tplWalkG dwalkRun at h ⊢
  simp only at h ⊢
  have hrel := relT_compressW h hri hci ⟨gateBase, (0, 0)⟩ dst0
    ⟨rfl, rfl, by simp [dst0], by simp [dst0]⟩
  generalize (dcompressW (rowI rw.size) (colI rw.size cw.size)).run dst0 = p at h hrel ⊢
  obtain ⟨r', s1⟩ := p
  generalize hl : accOps (colI rw.size cw.size) r' = l at h hrel ⊢
  have hp1 := dg_forM (fun t => dacc (rowI rw.size) t.1 t.2.1 t.2.2)
    (fun t => dg_acc (rowI rw.size) _ _ _) l s1
  obtain ⟨hDR, hOW⟩ := hrel hp1
  obtain ⟨hA, hB⟩ := acc_forM h (rowI rw.size) l s1 hDR.2.1 (List.prefix_refl _)
  subst hl
  simp only [List.map_cons, List.map_nil, Circ.encV, List.cons_append, List.nil_append]
  rw [hA, hB, ← hDR.2.2.1, ← hDR.2.2.2]
  unfold Eval.walkImpl Eval.walkABF
  have hop := outPairs_ev hOW
  have hin : ∀ k ∈ Eval.inPos, (rowI rw.size k).ev e = Eval.onPos rw (pos k) := fun k hk => by
    have : k < 2 ^ Blake2sCircuit.m := by
      simp only [Eval.inPos, List.mem_append, List.mem_range, List.mem_range'] at hk
      show k < 16384; omega
    rw [← hri, hpk k this]
  simp only [accOps, accC, List.map_append, List.sum_append, sum_flatMap', List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def, dvar, hci,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, zero_add, if_false, foldl_upd,
    Eval.foldl_add_eq, List.cons.injEq, and_true, sum_zero_map]
  have hin1 : (Eval.inPos.map fun x => (rowI rw.size x).ev e * Eval.onPos cw (pos x)) =
      Eval.inPos.map fun k => Eval.onPos rw (pos k) * Eval.onPos cw (pos k) :=
    List.map_congr_left fun k hk => by rw [hin k hk]
  have hin2 : (Eval.inPos.map fun x => (rowI rw.size x).ev e * Eval.onPos cw constPos) =
      Eval.inPos.map fun k => Eval.onPos rw (pos k) * Eval.onPos cw constPos :=
    List.map_congr_left fun k hk => by rw [hin k hk]
  have ho1 := congrArg List.sum (show (outPairs r').map (fun x => (rowI rw.size x.1.val).ev e *
      x.2.ev e) = ((outPairs r').map (fun p => (p.1, p.2.ev e))).map (fun q => Eval.onPos rw q.1 *
      q.2) by rw [List.map_map]; exact List.map_congr_left fun x _ => by simp [hri])
  have ho2 := congrArg List.sum (show (outPairs r').map (fun x => (rowI rw.size x.1.val).ev e *
      Eval.onPos cw constPos) = ((outPairs r').map (fun p => (p.1, p.2.ev e))).map (fun q =>
      Eval.onPos rw q.1 * Eval.onPos cw constPos) by
    rw [List.map_map]; exact List.map_congr_left fun x _ => by simp [hri])
  rw [hop] at ho1 ho2
  rw [hin1, hin2, hri constPos, ho1, ho2]
  simp only [List.sum_map_mul_right, List.sum_map_mul_left]
  constructor <;> ring

end Tpl
end FR
