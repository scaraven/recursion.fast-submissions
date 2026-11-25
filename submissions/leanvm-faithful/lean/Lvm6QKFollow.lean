-- New for lvm6 (WP CB). CB's programs against FORMAT6's schedule: the tree batch, the sponge caller
-- (with its core) and the sponge link commit nothing (`Stmt.noCommit`, CAND-decision), and the sponge
-- caller, core and link follow their part of `sched6` (ASM's `Follows`, ops by V1's walk).
import Lvm6QKStmt
import Lvm6AsmRing

/-!
# CB's programs: no commitment, and the schedule

* **`FollowsQ Q p os`**: ASM's `Follows` with a postcondition on the returned values (the sponge's
  layers need the claim's point length). `FollowsQ.follows`, `FollowsQ.bind`.
* Primitives against `opsOf L` of their items: `e2Reads`, `e2Sample`, `e2Samples`, `dDraws`,
  `gPoint`, the plain sumcheck (`rep R (rnd (count−1) g)`), the pack rounds, `layer6`, `layers6`,
  `kHead6`, `spongeEnd6`.
* **`spCaller6_follows`**: `Follows (spCaller6 h) (opsOf L (spItems h))` (`h ≥ 4`);
  **`ksLink_follows`**: `Follows (ksLinkProgE2 hk xl rows) (opsOf L (linkItems hk))`.
* **`treeProg_follows`**: `Follows (treeProg κ) (opsOf L (treeItems κ))` (`κ ≥ 4`).
* **`treeProg_noCommit`**, **`spCaller6_noCommit`**, **`ksLink_noCommit`**: `Stmt.noCommit`.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd Op Follows opsOf opsOf_append)

variable {α β : Type}

/-! ## `Follows` with a postcondition -/

/-- **`p` follows `os`, and every value it returns satisfies `Q`.** -/
def FollowsQ (Q : α → Prop) : VerifierProgram α → List Op → Prop
  | .ret a, os => os = [] ∧ Q a
  | .fail, _ => True
  | .grind _ _, _ => False
  | .read k, os => os.head? = some .rd ∧ ∀ x, FollowsQ Q (k x) os.tail
  | .sample k, os => os.head? = some .smp ∧ ∀ c, FollowsQ Q (k c) os.tail
  | .commit ht w k, os => os.head? = some (.cap ht w) ∧ FollowsQ Q k os.tail
  | .query i _ k, os => os.head? = some (.opn i) ∧ ∀ r, FollowsQ Q (k r) os.tail

theorem FollowsQ.follows {Q : α → Prop} :
    ∀ {p : VerifierProgram α} {os : List Op}, FollowsQ Q p os → Follows p os
  | .ret _, _, h => h.1
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => ⟨h.1, fun x ↦ (h.2 x).follows⟩
  | .sample _, _, h => ⟨h.1, fun c ↦ (h.2 c).follows⟩
  | .commit _ _ _, _, h => ⟨h.1, h.2.follows⟩
  | .query _ _ _, _, h => ⟨h.1, fun r ↦ (h.2 r).follows⟩

theorem FollowsQ.bind {P : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {o₁ o₂ : List Op} (hp : FollowsQ P p o₁) (hf : ∀ a, P a → FollowsQ Q (f a) o₂) :
    FollowsQ Q (p >>= f) (o₁ ++ o₂) := by
  induction p generalizing o₁ with
  | ret a =>
    obtain ⟨h, ha⟩ := hp
    subst h
    exact hf a ha
  | fail => trivial
  | grind _ _ _ => exact hp.elim
  | read k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun x ↦ ih x (h2 x)⟩
  | sample k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun c ↦ ih c (h2 c)⟩
  | commit ht w k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, ih h2⟩
  | query i ps k ih =>
    obtain ⟨h1, h2⟩ := hp
    cases o₁ with
    | nil => simp at h1
    | cons o os => exact ⟨by simpa using h1, fun r ↦ ih r (h2 r)⟩

theorem FollowsQ.congr {Q : α → Prop} {p : VerifierProgram α} {os os' : List Op} (h : os = os')
    (hp : FollowsQ Q p os) : FollowsQ Q p os' := h ▸ hp

/-- A last step that returns. -/
theorem FollowsQ.bind_ret {P : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {g : α → β} {o : List Op}
    (hp : FollowsQ P p o) (hg : ∀ a, P a → Q (g a)) : FollowsQ Q (p >>= fun a ↦ pure (g a)) o :=
  (FollowsQ.bind (f := fun a ↦ pure (g a)) (o₂ := []) hp fun a ha ↦
    (⟨rfl, hg a ha⟩ : FollowsQ Q (pure (g a)) [])).congr (List.append_nil o)

/-- A last step with no operations. -/
theorem FollowsQ.bind_nil {P : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {o : List Op} (hp : FollowsQ P p o) (hf : ∀ a, P a → FollowsQ Q (f a) []) : FollowsQ Q (p >>= f) o :=
  (FollowsQ.bind hp hf).congr (List.append_nil o)

theorem fq_require (c : Prop) [Decidable c] : FollowsQ (fun _ ↦ True) (VerifierProgram.require c) [] := by
  unfold VerifierProgram.require
  split
  · exact ⟨rfl, trivial⟩
  · trivial

/-- A check, then a value. -/
theorem fq_req_ret {Q : β → Prop} (c : Prop) [Decidable c] {a : β} (h : Q a) :
    FollowsQ Q (VerifierProgram.require c >>= fun _ ↦ pure a) [] :=
  FollowsQ.bind (o₁ := []) (o₂ := []) (fq_require c) fun _ _ ↦ (⟨rfl, h⟩ : FollowsQ Q (pure a) [])

theorem fq_readScalar : FollowsQ (fun _ ↦ True) VerifierProgram.readScalar [.rd] := ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

theorem fq_sample : FollowsQ (fun _ ↦ True) VerifierProgram.sampleChallenge [.smp] :=
  ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

/-! ## The primitives -/

variable (L : List V.Lev)

theorem ops_E (n : ℕ) : opsOf L [.E n] = List.replicate n .rd := by
  simp only [opsOf, V.Prims.walk, V.Prims.item, Lvm6.po_rep_rd]
  simp [Lvm6.PO]

theorem ops_D (n : ℕ) : opsOf L [.D n] = List.replicate n .smp := by
  simp only [opsOf, V.Prims.walk, V.Prims.item, Lvm6.po_rep_draw]
  simp [Lvm6.PO]

theorem ops_G (g : ℕ) : opsOf L [.G g] = [.rd, .smp] := rfl

theorem ops_rep (x : List Item) : ∀ m, opsOf L (rep m x) = (List.replicate m (opsOf L x)).flatten
  | 0 => rfl
  | m + 1 => by
    rw [show rep (m + 1) x = x ++ rep m x from rfl, opsOf_append, ops_rep x m]
    rfl

theorem fq_e2Read : FollowsQ (fun _ ↦ True) e2Read [.rd] := by
  unfold e2Read
  exact fq_readScalar.bind_ret fun _ _ ↦ trivial

theorem fq_e2Reads : ∀ n, FollowsQ (fun l : List E2 ↦ l.length = n) (e2Reads n) (opsOf L [.E n])
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    rw [ops_E, List.replicate_succ]
    exact FollowsQ.bind (o₁ := [.rd]) fq_e2Read fun _ _ ↦
      ((fq_e2Reads n).congr (ops_E L n)).bind_ret fun _ h ↦ by simp [h]

theorem fq_e2Sample (g : ℕ) (g' : ℕ) : FollowsQ (fun _ ↦ True) (e2Sample g) (opsOf L [.G g']) := by
  unfold e2Sample
  exact FollowsQ.bind (o₁ := [.rd]) (o₂ := [.smp]) fq_readScalar fun _ _ ↦
    FollowsQ.bind (o₁ := [.smp]) (o₂ := []) fq_sample fun _ _ ↦ fq_req_ret _ trivial

theorem fq_e2Samples (g g' : ℕ) : ∀ n,
    FollowsQ (fun l : List E2 ↦ l.length = n) (e2Samples g n) (opsOf L (rep n [.G g']))
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    rw [show rep (n + 1) [V.Item.G g'] = [.G g'] ++ rep n [.G g'] from rfl, opsOf_append]
    exact FollowsQ.bind (fq_e2Sample L g g') fun _ _ ↦ (fq_e2Samples g g' n).bind_ret fun _ h ↦ by simp [h]

theorem fq_dDraw : FollowsQ (fun _ ↦ True) dDraw [.smp] := by
  unfold dDraw
  exact fq_sample.bind_ret fun _ _ ↦ trivial

theorem fq_dDraws : ∀ n, FollowsQ (fun l : List E2 ↦ l.length = n) (dDraws n) (opsOf L [.D n])
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    rw [ops_D, List.replicate_succ]
    exact FollowsQ.bind (o₁ := [.smp]) fq_dDraw fun _ _ ↦
      ((fq_dDraws n).congr (ops_D L n)).bind_ret fun _ h ↦ by simp [h]

theorem fq_gPoint (g g' n : ℕ) :
    FollowsQ (fun l : List E2 ↦ l.length = n + 1) (gPoint g n) (opsOf L [.G g', .D n]) := by
  rw [show [V.Item.G g', .D n] = [.G g'] ++ [.D n] from rfl, opsOf_append]
  exact FollowsQ.bind (fq_e2Sample L g g') fun _ _ ↦ (fq_dDraws L n).bind_ret fun _ h ↦ by simp [h]

/-- A plain round's message (`count − 1` scalars). -/
theorem fq_roundNone (count : ℕ) (hc : 2 ≤ count) (claim : E2) :
    FollowsQ (fun _ ↦ True) (roundPolyE2 count claim none) (opsOf L [.E (count - 1)]) := by
  rw [ops_E, show count - 1 = (count - 2) + 1 by omega, List.replicate_succ]
  exact FollowsQ.bind (o₁ := [.rd]) fq_e2Read fun _ _ ↦
    ((fq_e2Reads L (count - 2)).congr (ops_E L _)).bind_ret fun _ _ ↦ trivial

/-- **The plain sumcheck**: `R` rounds `R(count − 1, ·)`. -/
theorem fq_sumcheck (g g' count : ℕ) (hc : 2 ≤ count) : ∀ (R : ℕ) (claim : E2),
    FollowsQ (fun res : List E2 × E2 ↦ res.1.length = R) (sumcheckE2 g claim count (List.replicate R none))
      (opsOf L (rep R (rnd (count - 1) g')))
  | 0, _ => ⟨rfl, rfl⟩
  | R + 1, claim => by
    rw [show rep (R + 1) (rnd (count - 1) g') = [.E (count - 1)] ++ ([.G g'] ++ rep R (rnd (count - 1) g'))
      from rfl, opsOf_append, opsOf_append]
    exact FollowsQ.bind (fq_roundNone L count hc claim) fun _ _ ↦ FollowsQ.bind (fq_e2Sample L g g') fun _ _ ↦
      (fq_sumcheck g g' count hc R _).bind_ret fun _ h ↦ by simp [h]

/-- **The pack rounds**: one `R(2, ·)` a coordinate. -/
theorem fq_pack (g g' : ℕ) : ∀ (rs : List E2) (value : E2),
    FollowsQ (fun res : E2 × List E2 ↦ res.2.length = rs.length) (packRoundsN g rs value)
      (opsOf L (rep rs.length (rnd 2 g')))
  | [], _ => ⟨rfl, rfl⟩
  | r :: rs, value => by
    rw [List.length_cons, show rep (rs.length + 1) (rnd 2 g') = [.E 2] ++ ([.G g'] ++ rep rs.length (rnd 2 g'))
      from rfl, opsOf_append, opsOf_append]
    refine FollowsQ.bind (?_ : FollowsQ (fun _ ↦ True) (roundPolyE2 3 value (some r)) _) fun _ _ ↦
      FollowsQ.bind (fq_e2Sample L g g') fun _ _ ↦ (fq_pack g g' rs _).bind_ret fun _ h ↦ by simp [h]
    exact (fq_e2Reads L 2).bind_ret fun _ _ ↦ trivial

theorem layer_items (κ : ℕ) : P18.layer κ =
    [.E 47] ++ ([.G 6] ++ (rep (κ - 3) (rnd 2 2) ++ (rep 11 (rnd 3 2) ++ ([.E 3] ++ [.G 2])))) := by
  simp only [Lvm6.Shape.layer, List.append_assoc]
  rfl

/-- **One layer** follows `P18.layer κ` on a claim whose point has `κ − 3` coordinates. -/
theorem fq_layer6 (κ step : ℕ) (cl : KClaim E2) (hpt : cl.point.length = κ - 3) :
    FollowsQ (fun c : KClaim E2 ↦ c.point.length = κ - 3) (layer6 κ step cl) (opsOf L (P18.layer κ)) := by
  rw [layer_items]
  simp only [opsOf_append]
  unfold layer6 layerTailE2N
  refine FollowsQ.bind (fq_e2Reads L 47) fun _ _ ↦ FollowsQ.bind (o₁ := []) (fq_require _) fun _ _ ↦
    FollowsQ.bind (fq_e2Sample L _ 6) fun _ _ ↦ ?_
  refine FollowsQ.bind ((fq_pack L _ 2 cl.point _).congr (by rw [hpt])) fun vp hvp ↦ ?_
  refine FollowsQ.bind (fq_sumcheck L _ 2 4 (by norm_num) 11 _) fun _ _ ↦ ?_
  exact FollowsQ.bind (fq_e2Reads L 3) fun _ _ ↦ FollowsQ.bind (o₁ := []) (fq_require _) fun _ _ ↦
    (fq_e2Sample L _ 2).bind_ret fun _ _ ↦ by simp only [hvp, hpt]

/-- **The layers** `steps`. -/
theorem fq_layers6 (κ : ℕ) : ∀ (steps : List ℕ) (cl : KClaim E2), cl.point.length = κ - 3 →
    FollowsQ (fun c : KClaim E2 ↦ c.point.length = κ - 3) (layers6 κ steps cl)
      (opsOf L (rep steps.length (P18.layer κ)))
  | [], _, hpt => ⟨rfl, hpt⟩
  | s :: steps, cl, hpt => by
    rw [List.length_cons, show rep (steps.length + 1) (P18.layer κ) = P18.layer κ ++ rep steps.length (P18.layer κ)
      from rfl, opsOf_append]
    exact FollowsQ.bind (fq_layer6 L κ s cl hpt) fun c hc ↦ fq_layers6 κ steps c hc

/-- The items of `kHead6` (§6.2 rows 6–9). -/
def headCoreItems (κ : ℕ) : List Item :=
  [.G 3, .D 5] ++ ([.E 1] ++ (rep 12 (P18.layer κ) ++ (rep 6 (rnd 2 2) ++ [.E 1])))

/-- **Rows 6–9** follow their items (`inst` of `P + 4` coordinates). -/
theorem fq_kHead6 (P base : ℕ) (inst output : List E2) (hi : inst.length = P + 4) :
    FollowsQ (fun hd : HeadOut ↦ hd.claim.point.length = P + 1) (kHead6 P base inst output)
      (opsOf L (headCoreItems (P + 4))) := by
  unfold kHead6 headCoreItems
  simp only [opsOf_append]
  refine FollowsQ.bind (fq_gPoint L _ 3 5) fun sl hsl ↦ FollowsQ.bind (fq_e2Read.congr (ops_E L 1).symm)
    fun cst _ ↦ ?_
  have hpt : (firstClaimSF Shape.v1 inst (sl.take 1) (sl.drop 1) output cst).point.length = P + 4 - 3 := by
    simp only [firstClaimSF, List.length_append, List.length_drop, List.length_take, hi, hsl]
    omega
  refine FollowsQ.bind ((fq_layers6 L (P + 4) (List.range 12) _ hpt).congr (by rw [List.length_range]))
    fun c hc ↦ ?_
  exact FollowsQ.bind (fq_sumcheck L _ 2 3 (by norm_num) 6 _) fun _ _ ↦
    (fq_e2Read.congr (ops_E L 1).symm).bind_nil fun _ _ ↦ fq_req_ret _ (by show c.point.length = P + 1; omega)

/-- **The sponge's input end** follows `spEndItems`. -/
theorem fq_spongeEnd6 (P : ℕ) (claim : KClaim E2) :
    FollowsQ (fun _ ↦ True) (spongeEnd6 P claim) (opsOf L (rep 10 (rnd 2 2)) ++ opsOf L [.E 64]) := by
  unfold spongeEnd6
  exact FollowsQ.bind (fq_sumcheck L _ 2 3 (by norm_num) 10 _) fun _ _ ↦
    (fq_e2Reads L 64).bind_nil fun _ _ ↦ fq_req_ret _ trivial

/-- **The tree's input end** follows `treeEndItems`. -/
theorem fq_treeEnd6 (P : ℕ) (claim : KClaim E2) :
    FollowsQ (fun _ ↦ True) (treeEnd6 P claim) (opsOf L (rep 11 (rnd 2 2)) ++ opsOf L [.E 64]) := by
  unfold treeEnd6
  exact FollowsQ.bind (fq_sumcheck L _ 2 3 (by norm_num) 11 _) fun _ _ ↦
    (fq_e2Reads L 64).bind_nil fun _ _ ↦ fq_req_ret _ trivial

theorem ops_K (n : ℕ) : opsOf L [.K n] = List.replicate n .rd := by
  simp only [opsOf, V.Prims.walk, V.Prims.item, Lvm6.po_rep_rd]
  simp [Lvm6.PO]

theorem fq_kRead : FollowsQ (fun _ ↦ True) kRead [.rd] := by
  unfold kRead
  exact fq_readScalar.bind_ret fun _ _ ↦ trivial

theorem fq_kReads : ∀ n, FollowsQ (fun l : List K ↦ l.length = n) (kReads n) (opsOf L [.K n])
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    rw [ops_K, List.replicate_succ]
    exact FollowsQ.bind (o₁ := [.rd]) fq_kRead fun _ _ ↦
      ((fq_kReads n).congr (ops_K L n)).bind_ret fun _ h ↦ by simp [h]

theorem spItems_eq (h : ℕ) : spItems h =
    rep h [.G 1] ++ ([.E 25] ++ (headCoreItems h ++ (rep 10 (rnd 2 2) ++ [.E 64]))) := by
  simp only [spItems, spCallerItems, coreItems, Shape.keccakCore, headCoreItems, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

theorem treeItems_eq (κ : ℕ) : treeItems κ = [.K 4] ++ ([.G 5, .D (κ - 2)] ++ ([.E 8] ++ ([.G 1] ++
    ([.E 21] ++ (headCoreItems κ ++ (rep 11 (rnd 2 2) ++ [.E 64])))))) := by
  simp only [treeItems, Shape.treePart, Shape.keccakCore, headCoreItems, List.append_assoc,
    List.cons_append, List.nil_append, show κ - 1 - 1 = κ - 2 by omega]
  rfl

theorem linkItems_eq (hk : ℕ) : linkItems hk = rep (hk + 5) [.G 1] ++ (rep hk (rnd 2 2) ++ [.E 4]) := by
  simp only [linkItems, List.append_assoc]

/-- **The tree batch follows `treeItems κ`** (FORMAT6 §6.2). -/
theorem treeProg_follows (κ : ℕ) (hκ : 4 ≤ κ) : Follows (treeProg κ) (opsOf L (treeItems κ)) := by
  refine FollowsQ.follows (Q := fun _ ↦ True) ?_
  rw [treeItems_eq]
  simp only [opsOf_append]
  unfold treeProg
  refine FollowsQ.bind (fq_kReads L 4) fun _ _ ↦ FollowsQ.bind (fq_gPoint L _ 5 (κ - 2)) fun ρ hρ ↦
    FollowsQ.bind (fq_e2Reads L 8) fun _ _ ↦ FollowsQ.bind (fq_e2Sample L _ 1) fun u _ ↦
    FollowsQ.bind (fq_e2Reads L 21) fun _ _ ↦ ?_
  rw [show headCoreItems κ = headCoreItems (κ - 4 + 4) by rw [Nat.sub_add_cancel hκ]]
  exact FollowsQ.bind (fq_kHead6 L (κ - 4) 8 (u :: ρ) _ (by simp only [List.length_cons, hρ]; omega))
    fun _ _ ↦ (fq_treeEnd6 L _ _).bind_ret fun _ _ ↦ trivial

/-- **The sponge caller and its core follow `spItems h`** (FORMAT6 §T and §6.3). -/
theorem spCaller6_follows (h : ℕ) (hh : 4 ≤ h) : Follows (spCaller6 h) (opsOf L (spItems h)) := by
  refine FollowsQ.follows (Q := fun _ ↦ True) ?_
  rw [spItems_eq]
  simp only [opsOf_append]
  unfold spCaller6 spongeCore6
  refine FollowsQ.bind (fq_e2Samples L _ 1 h) fun r hr ↦ FollowsQ.bind (fq_e2Reads L 25) fun _ _ ↦ ?_
  rw [show headCoreItems h = headCoreItems (h - 4 + 4) by rw [Nat.sub_add_cancel hh]]
  exact (FollowsQ.bind (Q := fun _ ↦ True) (fq_kHead6 L (h - 4) 25 r _ (by omega)) fun _ _ ↦
    (fq_spongeEnd6 L _ _).bind_ret (Q := fun _ ↦ True) fun _ _ ↦ trivial).bind_ret fun _ _ ↦ trivial

/-- **The sponge link follows `linkItems hk`** (FORMAT6 §T). -/
theorem ksLink_follows (hk xl : ℕ) (rows : List ℕ) :
    Follows (ksLinkProgE2 hk xl rows) (opsOf L (linkItems hk)) := by
  refine FollowsQ.follows (Q := fun _ ↦ True) ?_
  rw [linkItems_eq, opsOf_append, opsOf_append]
  unfold ksLinkProgE2
  exact FollowsQ.bind (fq_e2Samples L _ 1 _) fun _ _ ↦ FollowsQ.bind (fq_sumcheck L _ 2 3 (by norm_num) hk _)
    fun _ _ ↦ (fq_e2Reads L 4).bind_nil fun _ _ ↦ fq_req_ret _ trivial

/-! ## No commitment -/

open VerifierProgram in
theorem nc_of_follows {p : VerifierProgram α} {os : List Op} (h : Follows p os)
    (hc : ∀ ht w, Op.cap ht w ∉ os) : Stmt.noCommit p := fun _ _ hr ↦ NoCommit.reach_commits (h.noCommit hc) hr

/-- The items whose ops are reads and draws only. -/
def simpleB : Item → Bool
  | .E _ => true
  | .K _ => true
  | .G _ => true
  | .D _ => true
  | _ => false

/-- All items simple. -/
def AllS (its : List Item) : Prop := ∀ it ∈ its, simpleB it = true

theorem ops_nocap : ∀ its : List Item, AllS its → ∀ ht w, Op.cap ht w ∉ opsOf L its
  | [], _, _, _ => by simp [opsOf, V.Prims.walk, Lvm6.PO]
  | it :: its, hs, ht, w => by
    rw [show it :: its = [it] ++ its from rfl, opsOf_append, List.mem_append, not_or]
    refine ⟨?_, ops_nocap its (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx)) ht w⟩
    have h0 := hs it List.mem_cons_self
    cases it with
    | E n => rw [ops_E]; simp [List.mem_replicate]
    | K n => rw [ops_K]; simp [List.mem_replicate]
    | G g => rw [ops_G]; simp
    | D n => rw [ops_D]; simp [List.mem_replicate]
    | _ => simp [simpleB] at h0

theorem allS_append {a b : List Item} (ha : AllS a) (hb : AllS b) : AllS (a ++ b) := by
  intro it hit
  rcases List.mem_append.mp hit with h | h
  exacts [ha it h, hb it h]

theorem allS_rep {x : List Item} (hx : AllS x) (m : ℕ) : AllS (rep m x) := by
  intro it hit
  simp only [rep, List.mem_flatten, List.mem_replicate] at hit
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
  exact hx it hl

theorem allS_rnd (n g : ℕ) : AllS (rnd n g) := by simp [AllS, rnd, simpleB]

theorem allS_layer (κ : ℕ) : AllS (P18.layer κ) := by
  rw [layer_items]
  exact allS_append (by simp [AllS, simpleB]) (allS_append (by simp [AllS, simpleB]) (allS_append (allS_rep (allS_rnd 2 2) _)
    (allS_append (allS_rep (allS_rnd 3 2) _) (by simp [AllS, simpleB]))))

theorem allS_head (κ : ℕ) : AllS (headCoreItems κ) :=
  allS_append (by simp [AllS, simpleB]) (allS_append (by simp [AllS, simpleB]) (allS_append (allS_rep (allS_layer κ) _)
    (allS_append (allS_rep (allS_rnd 2 2) _) (by simp [AllS, simpleB]))))

/-- **The tree batch commits nothing.** -/
theorem treeProg_noCommit (κ : ℕ) (hκ : 4 ≤ κ) : Stmt.noCommit (treeProg κ) := by
  refine nc_of_follows (treeProg_follows [] κ hκ) (ops_nocap [] _ ?_)
  rw [treeItems_eq]
  exact allS_append (by simp [AllS, simpleB]) (allS_append (by simp [AllS, simpleB]) (allS_append (by simp [AllS, simpleB])
    (allS_append (by simp [AllS, simpleB]) (allS_append (by simp [AllS, simpleB]) (allS_append (allS_head κ)
      (allS_append (allS_rep (allS_rnd 2 2) _) (by simp [AllS, simpleB])))))))

/-- **The sponge caller and its core commit nothing.** -/
theorem spCaller6_noCommit (h : ℕ) (hh : 4 ≤ h) : Stmt.noCommit (spCaller6 h) := by
  refine nc_of_follows (spCaller6_follows [] h hh) (ops_nocap [] _ ?_)
  rw [spItems_eq]
  exact allS_append (allS_rep (by simp [AllS, simpleB]) _) (allS_append (by simp [AllS, simpleB]) (allS_append (allS_head h)
    (allS_append (allS_rep (allS_rnd 2 2) _) (by simp [AllS, simpleB]))))

/-- **The sponge link commits nothing.** -/
theorem ksLink_noCommit (hk xl : ℕ) (rows : List ℕ) : Stmt.noCommit (ksLinkProgE2 hk xl rows) := by
  refine nc_of_follows (ksLink_follows [] hk xl rows) (ops_nocap [] _ ?_)
  rw [linkItems_eq]
  exact allS_append (allS_rep (by simp [AllS, simpleB]) _) (allS_append (allS_rep (allS_rnd 2 2) _) (by simp [AllS, simpleB]))

end Lvm6.QK
