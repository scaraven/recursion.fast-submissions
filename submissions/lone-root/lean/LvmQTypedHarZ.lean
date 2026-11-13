-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's zerocheck and wiring phases: `zeroG` replays V_S's `dZeroT`,
-- `wireG` replays `dWiringT` (with `virtG`'s value: V_S's closed form `virtEF` on the circuit's regions).
import LvmQTypedHarB

/-!
# The zerocheck and the wiring sumcheck in the circuit

* **`zeroG_replays`**: `zeroG z g P` (gate on) replays `dZeroT` from `P` to `wGP P`: `r_x` is the run's challenge
  cells, `a*, b*, c*` its three loaded cells.
* **`virtG_spec`**: `virtG`'s value is V_S's `virtEF` (the `PUB` region's extension at `r_y` times its selector,
  plus the word `1`'s selector), on regions that are V_S's (`TdOk`).
* **`wireG_replays`**: `wireG` replays `dWiringT` from `wGP P` to `rRP P`: `r_y`, the matrix values `v_o` and the
  region values are its cells.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)

section
variable {c : Ctx} {M : Mem}

/-- A gadget's soundness at one pointer. -/
def z_SoundAt {α : Type} (c : Ctx) (M : Mem) (g : BM α) (p : Ptr) (Φ : α → Prop) : Prop :=
  SegsHold c M p (g p).2 → SegsAssert M p (g p).2 → Φ (g p).1

theorem z_soundAt_bind {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr} {Φ : α → Prop} {Ψ : β → Prop}
    (hm : z_SoundAt c M m p Φ) (hf : ∀ x, Φ x → z_SoundAt c M (f x) (p.adv (m p).2) Ψ) :
    z_SoundAt c M (m >>= f) p Ψ := fun hH hA => by
  rw [hold_bind] at hH
  rw [assert_bind] at hA
  rw [bind_apply]
  exact hf _ (hm hH.1 hA.1) hH.2 hA.2

theorem z_soundAt_getPtr {β : Type} {f : Ptr → BM β} {p : Ptr} {Ψ : β → Prop}
    (h : z_SoundAt c M (f p) p Ψ) : z_SoundAt c M (getPtr >>= f) p Ψ := fun hH hA => by
  simp only [getPtr, bind_apply, Ptr.adv_nil, List.nil_append] at hH hA ⊢
  exact h hH hA

theorem z_soundAt_pure {α : Type} {x : α} {p : Ptr} {Φ : α → Prop} (h : Φ x) : z_SoundAt c M (pure x) p Φ :=
  fun _ _ => h

theorem z_soundAt_of {α : Type} {g : BM α} {Φ : α → Prop} (h : SoundG c M g Φ) (p : Ptr) : z_SoundAt c M g p Φ :=
  h p

theorem z_replays_of {α β : Type} {sig : ByteArray} {F : DM α} {g : BM β} {p : Ptr} {P P' : Nat}
    {R : α → β → Prop} (h : z_SoundAt c M g p fun out => ∀ s : RS, pos s = P → s.ok = true →
      (F sig s).2.ok = true ∧ pos (F sig s).2 = P' ∧ R (F sig s).1 out) :
    Replays c M sig F g p P P' R := fun hok => h hok.1 hok.2

theorem z_getD_vs (l : List Cell) (z : Cell) (i : Nat) : (l.getD i z).val M = (vs M l).getD i (z.val M) := by
  simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- Equality-mode rounds of count 3 on `n` consecutive factor cells from `eb`, at the pointer `q`. -/
theorem z_scQ3_at (hS : Streamed M sig T) (n L₀ eb : Nat) (cl : Cell) (q : Ptr) (pt : List FE)
    (hpt : pt.length = n) (hP : ∀ i < n, M.e (eb + i) = pt.getD i 0) (hT : L₀ + 15 * n ≤ T) :
    z_SoundAt c M (QB.scRunQ3 (binParts n) L₀ (fun i => eb + i) (fun _ => 1) cl) q fun fin =>
      ∀ s : RS, s.msg = 0 → s.ent = 8 * L₀ →
        fin.val M = (sumcheck (cl.val M) 3 (pt.map some) sig s).1.2 ∧
        ∀ i < n, M.e (q.e + 3 + 7 * i) = (sumcheck (cl.val M) 3 (pt.map some) sig s).1.1.getD i 0 := by
  intro hH _ s hs hent
  have := QB.scRunQ3_eq (binParts n) L₀ (fun i => eb + i) (fun _ => 1) cl q hH sig s hs hent pt
    (by rw [nRounds_binParts]; exact hpt) (fun i₀ d hm jf hjf => by
      have := QB.chunk_lt _ 0 i₀ d hm jf hjf
      rw [nRounds_binParts] at this
      rw [one_mul, Nat.add_assoc]; exact hP _ (by omega))
    (fun j _ h2 => by rw [nRounds_binParts] at h2; exact hS j (by omega))
  rw [nRounds_binParts] at this
  exact ⟨this.1, fun i hi => by rw [← this.2 i hi]; congr 1; omega⟩


/-- **The zerocheck replayed** (soundness direction): wherever `zeroG`'s rows hold and assert (gate on), `dZeroT`
from any state at position `P` with `ok` keeps `ok`, ends at `wGP P`; `r_x` is the output's first list's values,
`a*, b*, c*` the second's. -/
theorem zeroG_replays (hS : Streamed M sig T) {z g : Cell} (hz : z.val M = 0) (hzE : z.ty = .E)
    (hg : g.val M = 1) (hgK : g.ty = .K) {P : Nat} (hP : P % 8 = 0) (hT : wGP P + 40 ≤ 8 * T) (ptr : Ptr)
    (hp : 1 ≤ ptr.e) :
    Replays c M sig TypedV.dZeroT (zeroG z g P) ptr P (wGP P) fun v t =>
      v.1 = vs M t.1 ∧ v.2.1 = (t.2.getD 0 z).val M ∧ v.2.2.1 = (t.2.getD 1 z).val M ∧
        v.2.2.2 = (t.2.getD 2 z).val M ∧ t.1.length = 20 ∧ (∀ x ∈ t.1, x.ty = .E) := by
  have hW : wGP P = P + 3912 := by simp only [wGP, zAbcP, zRP, tX]
  rw [hW] at hT ⊢
  refine z_replays_of ?_
  unfold zeroG
  refine z_soundAt_bind (z_soundAt_of (ldEsP_sound hS ((P + 40) / 8) 9 tX fun i hi => by simp only [tX] at hi; omega) _)
    fun tb htb => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scQ3_at hS tX _ tb.1 z _ ((List.range tX).map fun i => feAt sig (P + 40 + 72 * i))
    (by simp) (fun i hi => by rw [htb.2 i hi, QB.getD_map_range _ _ hi]; congr 1; omega)
    (by simp only [zRP, tX]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (ldEs_sound hS ((zAbcP P + 40) / 8) 3 3 fun i hi => by
    simp only [zAbcP, zRP, tX]; omega) _) fun abc habc => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t ht => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dZeroT, Q1.bind_run, Q1.samples_run sig _ s (by decide : 1 ≤ Lvm.Typed.xVars), Q1.pure_run,
    Q1.readEs_run, require_run, hs, hok]
  rw [hz] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 72 * tX, 0, true⟩ rfl (by simp only [zRP]; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) 0 ⟨P + 72 * tX, 0, true⟩ rfl)
  have hlen := sumcheck_len 0 3 (by decide)
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) sig ⟨P + 72 * tX, 0, true⟩ rfl
  generalize sumcheck 0 3 _ sig _ = R at h1 h2 hst hlen ⊢
  rw [hst]
  have hab : scalarsAt (feAt sig) (P + 72 * tX + QB.entB (3 - 1) * tX + 0 + 40) 3 = vs M abc := by
    rw [habc, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [zAbcP, zRP, tX, QB.entB]; omega
  simp only [List.length_map, List.length_range] at hst hlen ⊢
  rw [hab]
  rw [z_getD_vs abc z, z_getD_vs abc z, z_getD_vs abc z, hz] at ht ⊢
  have hfa := (QB.gate_eq_iff hg _ _).mp hA.2
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, trivial, ?_⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, hfa, ht.1]
  · simp only [pos, QB.entB, tX]
  · apply List.ext_getElem (by simp [vs, hlen])
    intro i h1' h2'
    simp only [vs, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply, Cell.val_E]
    rw [h2 i (by simpa [hlen] using h1'), List.getD_eq_getElem _ _ h1']
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl

/-! ## Values without assertions -/

/-- A gadget's value at one pointer, from its rows alone. -/
def z_HoldAt {α : Type} (c : Ctx) (M : Mem) (g : BM α) (p : Ptr) (Φ : α → Prop) : Prop :=
  SegsHold c M p (g p).2 → Φ (g p).1

theorem z_holdAt_bind {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr} {Φ : α → Prop} {Ψ : β → Prop}
    (hm : z_HoldAt c M m p Φ) (hf : ∀ x, Φ x → z_HoldAt c M (f x) (p.adv (m p).2) Ψ) :
    z_HoldAt c M (m >>= f) p Ψ := fun hH => by
  rw [hold_bind] at hH
  rw [bind_apply]
  exact hf _ (hm hH.1) hH.2

theorem z_holdAt_mulAdd (τ : Ty) (a b d : Cell) (p : Ptr) :
    z_HoldAt c M (mulAdd τ a b d) p fun r => r.val M = a.val M * b.val M + d.val M := mulAdd_spec

theorem z_holdAt_lin (τ : Ty) (k k' : FK) (a b : Cell) (p : Ptr) :
    z_HoldAt c M (lin τ k k' a b) p fun r => r.val M = a.val M + FE.ofK k * b.val M + FE.ofK k' := lin_spec

/-- **`eqConstG`'s value**: `eq(r, b)` at the cells' values (`eqAtF`). -/
theorem z_eqConstG_hold {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (rs : List Cell) (b : Nat) (p : Ptr),
      z_HoldAt c M (eqConstG z o rs b) p fun t => t.val M = Lvm.eqAtF (vs M rs) b
  | [], b, p => fun _ => by simp [eqConstG, pure_apply, Lvm.eqAtF, ho, vs]
  | r :: rs, b, p => by
    simp only [eqConstG]
    refine z_holdAt_bind (z_eqConstG_hold hz ho rs (b / 2) p) fun t ht => ?_
    simp only [vs, List.map_cons, Lvm.eqAtF] at ht ⊢
    split_ifs with hb
    · refine fun h => (z_holdAt_mulAdd .E t r z _ h).trans ?_
      rw [ht, hz, add_zero, mul_comm]
    · refine z_holdAt_bind (z_holdAt_lin _ 0 1 r r _) fun u hu => fun h => (z_holdAt_mulAdd .E t u z _ h).trans ?_
      rw [ht, hz, add_zero, hu, ofK_zero, ofK_one, zero_mul, add_zero, mul_comm, add_comm]


theorem z_holdAt_pure {α : Type} {x : α} {p : Ptr} {Φ : α → Prop} (h : Φ x) : z_HoldAt c M (pure x) p Φ :=
  fun _ => h

/-- A fold adding one term per item is the sum of the terms. -/
theorem z_foldl_add_of {ι : Type} {F : FE → ι → FE} (t : ι → FE) (hF : ∀ acc x, F acc x = acc + t x) :
    ∀ (l : List ι) (a : FE), l.foldl F a = a + (l.map t).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, z_foldl_add_of t hF l, hF, List.map_cons, List.sum_cons, add_assoc]

theorem z_sum_map_ite {ι : Type} (q : ι → Bool) (A : ι → FE) :
    ∀ l : List ι, (l.map fun x => if q x then A x else 0).sum = ((l.filter q).map A).sum
  | [] => rfl
  | x :: l => by by_cases h : q x <;> simp [h, z_sum_map_ite q A l]

/-- **`virtEF` on V_S's regions** (`TdOk`): the `PUB` region's term and the word `1`'s selector. -/
theorem z_virtEF_td {Td : TData} {N : TNat} (htd : TdOk Td N) (pub : Pub) (ry : List FE) :
    TypedV.virtEF N pub ry = TypedV.hiW ry 10 Td.pub *
      TypedV.mleK 10 (fun i => pub.hdrLanes.toArray.getD (0 + i) 0) ry + TypedV.hiW ry 0 Td.one := by
  simp only [TypedV.virtEF]
  rw [z_foldl_add_of (fun g => (if g.src == .pub then TypedV.hiW ry g.log g.base *
      TypedV.mleK g.log (fun i => pub.hdrLanes.toArray.getD (g.dst + i) 0) ry else 0) +
      (if g.src == .one then TypedV.hiW ry g.log g.base else 0)) (fun acc g => ?_)]
  · rw [zero_add, List.sum_map_add, z_sum_map_ite, z_sum_map_ite]
    have hP := htd.pub
    have hO := htd.one
    simp only [TNat.regsOf] at hP hO
    rw [hP, show ∀ l : List TypedV.NReg, l.map (fun g => TypedV.hiW ry g.log g.base) =
      (l.map fun g => (g.base, g.log)).map fun x => TypedV.hiW ry x.2 x.1 from fun l => by rw [List.map_map]; rfl, hO]
    simp
  · rcases g with ⟨b, l, s, d⟩
    cases s <;> simp

/-- `mleK` of `K` values at a point of `≥ 10` coordinates is `pubEval` at its first 10. -/
theorem z_mleK_pub (vals : List FK) (pt : List FE) (hl : 10 ≤ pt.length) :
    TypedV.mleK 10 (fun i => vals.toArray.getD (0 + i) 0) pt = M3.pubEval vals (pt.take 10) := by
  have hlen : (pt.take 10).length = 10 := by simp; omega
  rw [M3.pubEval_eq, mle_eq_sum, hlen, TypedV.mleK, z_foldl_add_of _ (fun _ _ => rfl), zero_add, list_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [FE.smulBase_eq_mul, eqKernelA_getD _ (by rw [hlen]; exact hi), M3.toArray_getD, Nat.zero_add, M3.pubCell,
    mul_comm]


end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **`virtG`'s value is V_S's `virtEF`** at `r_y` (the child's `PUB` from the stream's header lanes and the current
proof's `vk` cells at `pb + 1`), on regions that are V_S's. -/
theorem virtG_spec (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr) (h : SegsHold c M q (virtG z o Td pb ry q).2) :
    (virtG z o Td pb ry q).1.val M = TypedV.virtEF N (pubOf vk cL sig) (vs M ry) := by
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp only at hoE; subst hoE; rfl
  have hal : ∀ i, (ry.getD i z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : ry[i]? with
    | none => exact hzE
    | some y => exact hryE y (List.mem_of_getElem? h)
  have hvl : (vs M ry).length = 21 := by simp [vs, hry]
  have hpt : (List.range 10).map (fun i => (ry.getD i z).val M) = (vs M ry).take 10 := by
    apply List.ext_getElem (by simp [hvl])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take, z_getD_vs, List.getD_eq_getElem _ _ (by omega)]
  have hqp : ∀ p : Ptr, z_HoldAt c M (Lvm.QAcc.qpub (fun i => ry.getD i z) z o 10 11 (pb + 1) pubLanes) p
      fun v => v.val M = M3.pubEval (pubOf vk cL sig).hdrLanes ((vs M ry).take 10) := fun p h => by
    refine (Lvm.QAcc.qpub_spec hz hal hone (by decide) h).trans ?_
    rw [hpt, Lvm.QAcc.pubEval_child hS hH cL hvk _ (by rw [List.length_take, hvl]; decide)]
  have key : z_HoldAt c M (virtG z o Td pb ry) q fun w => w.val M = TypedV.hiW (vs M ry) 10 Td.pub *
      M3.pubEval (pubOf vk cL sig).hdrLanes ((vs M ry).take 10) + TypedV.hiW (vs M ry) 0 Td.one := by
    simp only [virtG, regSelG, htd.qlt, Lvm.Loop.Build.add]
    refine z_holdAt_bind (z_eqConstG_hold hz ho _ _ _) fun sP hsP => ?_
    refine z_holdAt_bind (hqp _) fun vP hvP => ?_
    refine z_holdAt_bind (z_holdAt_mulAdd .E sP vP z _) fun w hw => ?_
    refine z_holdAt_bind (z_eqConstG_hold hz ho ry Td.one _) fun e1 he1 => ?_
    refine z_holdAt_bind (z_holdAt_lin _ 1 0 w e1 _) fun w' hw' => z_holdAt_pure ?_
    rw [hw', ofK_one, ofK_zero, one_mul, add_zero, hw, hz, add_zero, hsP, hvP, he1]
    simp only [TypedV.hiW, vs, List.map_drop, List.drop_zero, Nat.shiftRight_zero]
  rw [key h, z_virtEF_td htd, z_mleK_pub _ _ (by omega)]


theorem z_virtG_at (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr) :
    z_SoundAt c M (virtG z o Td pb ry) q fun w => w.val M = TypedV.virtEF N (pubOf vk cL sig) (vs M ry) :=
  fun h _ => virtG_spec vk cL hS hH hz ho hzE hoE htd hvk ry hry hryE q h

/-- Plain rounds of count 3, at the pointer `q`: the final claim and the challenge cells. -/
theorem z_scP3_at (hS : Streamed M sig T) (n L₀ : Nat) (cl : Cell) (q : Ptr) (hT : L₀ + 15 * n ≤ T) :
    z_SoundAt c M (QB.scRunP3 (binParts n) L₀ cl) q fun fin => ∀ s : RS, s.msg = 0 → s.ent = 8 * L₀ →
      fin.val M = (sumcheck (cl.val M) 3 (List.replicate n none) sig s).1.2 ∧
      (sumcheck (cl.val M) 3 (List.replicate n none) sig s).1.1 =
        vs M ((List.range n).map fun i => ec (q.e + 3 + 6 * i)) := by
  intro hH _ s hs hent
  have := QB.scRunP3_eq (binParts n) L₀ cl q hH sig s hs hent
    (fun j _ h2 => by rw [nRounds_binParts] at h2; exact hS j (by omega))
  rw [nRounds_binParts] at this
  have hl := sumcheck_len (cl.val M) 3 (by decide) (List.replicate n none) sig s hs
  rw [List.length_replicate] at hl
  refine ⟨this.1, List.ext_getElem (by simp [vs, hl]) fun i h1 _ => ?_⟩
  rw [← List.getD_eq_getElem _ 0 h1, ← this.2 i (by omega)]
  simp only [vs, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply, Cell.val_E]
  congr 1; omega

theorem z_ldE_at (hS : Streamed M sig T) {a : Nat} (ha : a + 2 < T) (p : Ptr) :
    z_SoundAt c M (Lvm.QAcc.ldE a) p fun x => x.val M = feAt sig (8 * a) :=
  fun h _ => Lvm.QAcc.ldE_feAt hS ha h

/-- `ldEs`'s values, and its cells are `E` cells. -/
theorem z_ldEs_soundE (hS : Streamed M sig T) (a st n : Nat) (ha : ∀ i < n, a + st * i + 2 < T) :
    SoundG c M (ldEs a st n) fun xs =>
      vs M xs = (List.range n).map (fun i => feAt sig (8 * (a + st * i))) ∧ ∀ x ∈ xs, x.ty = .E :=
  fun p hH hA => ⟨ldEs_sound hS a st n ha p hH hA, by
    rw [(ldEs_sound_at hS st n a p ha hH).1]
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl⟩

/-- **The wiring sumcheck replayed**: wherever `wireG`'s rows hold and assert (gate on), `dWiringT` on the
zerocheck's values (`abc`'s cells) from any state at `wGP P` with `ok` keeps `ok`, ends at `rRP P`; `r_y`, the
matrix values and the region values are the output's cells' values. -/
theorem wireG_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {z o g : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1)
    (hgK : g.ty = .K) {Td : TData} {N : TNat} (htd : TdOk Td N) {pb : Nat}
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {P : Nat} (hP : P % 8 = 0)
    (hT : rRP P + 40 ≤ 8 * T) (abc : List Cell) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig
      (TypedV.dWiringT N (pubOf vk cL sig) ((abc.getD 0 z).val M, (abc.getD 1 z).val M, (abc.getD 2 z).val M))
      (wireG z o g Td pb P abc) ptr (wGP P) (rRP P) fun v t =>
        v.1 = vs M t.1 ∧ v.2.1 = vs M t.2.1 ∧ v.2.2 = vs M t.2.2 ∧ t.1.length = 21 ∧ (∀ x ∈ t.1, x.ty = .E) ∧
          t.2.1.length = 4 ∧ (∀ x ∈ t.2.1, x.ty = .E) ∧ t.2.2.length = 4 ∧ (∀ x ∈ t.2.2, x.ty = .E) := by
  have hW : wGP P = P + 3912 := by simp only [wGP, zAbcP, zRP, tX]
  have hR : rRP P = P + 6696 := by simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, tX, tY]
  have hV : wVP P = P + 6504 := by simp only [wVP, wRP, wGP, zAbcP, zRP, tX, tY]
  have hRP : wRP P = P + 3984 := by simp only [wRP, wGP, zAbcP, zRP, tX]
  rw [hR] at hT
  rw [hW, hR]
  refine z_replays_of ?_
  unfold wireG
  rw [hW, hV, hRP]
  refine z_soundAt_bind (z_ldE_at hS (a := (P + 3912 + 40) / 8) (by omega) _) fun γ hγ => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun u hu => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun c0 hc0 => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scP3_at hS tY ((P + 3984) / 8) c0 _ (by simp only [tY]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6504 + 40) / 8) 3 4 fun i hi => by omega) _)
    fun vC hvC => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6504 + 40) / 8 + 12) 3 4 fun i hi => by omega) _)
    fun rC hrC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ 1 0 _ _)) _) fun dw hdw => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m1 hm1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m2 hm2 => ?_
  refine z_soundAt_bind (z_virtG_at vk cL hS hH hz ho hzE hoE htd hvk _ (by simp) (by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl) _) fun ve hve => ?_
  refine z_soundAt_bind (z_soundAt_of (sumG_sound hz _) _) fun sC hsC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun pr hpr => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dWiringT, Q1.bind_run, Q1.sampleE_run, Q1.pure_run, Q1.readEs_run, require_run, hok]
  have e1 : s.ent + 40 + s.msg = P + 3912 + 40 := by omega
  have e2 : s.ent + 72 + s.msg = P + 3984 := by omega
  rw [e1, e2]
  have hγ' : γ.val M = feAt sig (P + 3912 + 40) := by rw [hγ]; congr 1; omega
  have hcl : c0.val M = (abc.getD 0 z).val M + feAt sig (P + 3912 + 40) * (abc.getD 1 z).val M +
      feAt sig (P + 3912 + 40) * feAt sig (P + 3912 + 40) * (abc.getD 2 z).val M := by
    rw [hc0.1, hu.1, hγ']; ring
  rw [hcl] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 3984, 0, true⟩ rfl (by dsimp only; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig (List.replicate tY none) (c0.val M) ⟨P + 3984, 0, true⟩ rfl)
  have hlen := sumcheck_len (c0.val M) 3 (by decide) (List.replicate tY none) sig ⟨P + 3984, 0, true⟩ rfl
  rw [hcl] at hlen hst
  generalize sumcheck _ 3 _ sig _ = R at h1 h2 hst hlen ⊢
  simp only [List.length_replicate] at hst hlen
  rw [hst]
  rw [← h2] at hve
  have hv : ∀ s' : RS, s' = ⟨P + 3984 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + s'.msg + 40) 4 = vs M vC := by
    rintro s' rfl
    rw [hvC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  have hr : ∀ s' : RS, s' = ⟨P + 3984 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + (s'.msg + 24 * 4) + 40) 4 = vs M rC := by
    rintro s' rfl
    rw [hrC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  rw [hv _ rfl, hr _ rfl]
  dsimp only
  simp only [z_getD_vs vC z, hz] at hdw hm1 hm2
  have hsC' : sC.val M = sumE (vs M rC) + ve.val M := by
    rw [hsC, show vs M (rC ++ [ve]) = vs M rC ++ [ve.val M] by simp [vs], sumE_append, sumE_cons, sumE_nil,
      add_zero]
  refine ⟨?_, ?_, h2, rfl, rfl, by simp, ?_, ?_, hvC.2, ?_, hrC.2⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, (QB.gate_eq_iff hg _ _).mp hA.2, hpr.1, hz, add_zero, hsC', hve,
      hm2.1, hm1.1, hdw.1, hγ', ofK_one, ofK_zero, one_mul, add_zero]
    ring
  · simp only [pos, QB.entB, tY]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl
  · simpa [vs] using congrArg List.length hvC.1
  · simpa [vs] using congrArg List.length hrC.1

end

end Lvm.Har
