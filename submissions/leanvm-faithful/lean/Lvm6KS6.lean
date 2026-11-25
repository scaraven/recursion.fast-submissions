-- New for lvm6 K2: the tree phase of `prog6` (`treeProgS6`): its doom transfer (from K1's `treeSpecS`), its
-- schedule (ASM's `PhasesFollow.tree`: it follows `Shape.treePart`) and that it commits nothing.
import Lvm6AsmProg
import Lvm6KProgS6
import Lvm6KTreeSpec
import Lvm6KNoCommit

/-!
# `treeProgS6`: spec, schedule, no commitment

* **`treeSpecS6 : Stmt.treeSpec treeProgS6`**: on the shapes where the four constants hold,
  `treeProgS6` is `treeProgS29` (`treeProgS6_eq`, by definition), so K1's `treeSpecS`; elsewhere it
  rejects.
* **`treeProgS6_follows sh x : Follows (treeProgS6 sh x) (opsOf sh.levs sh.treePart)`**, ASM's
  `PhasesFollow.tree` field. The program side is computed by `FollowsQ` (`Follows` with a property
  of the returned value: the lengths of `ρ`, `r_seg :: r_lane` and the claim's point fix the number
  of pack rounds in each layer); `treePart_ops` computes `opsOf` of `Shape.treePart` under the four
  shape facts.
* **`treeProgS6_noCommit sh x : Stmt.noCommit (treeProgS6 sh x)`**.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm6.KPack

/-! ## The spec -/

theorem treeProgS6_eq (sh : Lvm6.Shape) (x : Lvm6.Hdr) :
    treeProgS6 sh x = if TreeShapeOK sh then treeProgS29 sh x else VerifierProgram.fail := rfl

/-- **T2 for `prog6`'s tree phase**: `Stmt.treeSpec treeProgS6`. -/
theorem treeSpecS6 : Stmt.treeSpec treeProgS6 := by
  intro sh x
  rw [treeProgS6_eq]
  split_ifs
  · exact treeSpecS sh x
  · intro C R G _ _
    exact ⟨Spec.fail⟩

/-! ## No commitment -/

/-- **The tree phase commits nothing.** -/
theorem treeProgS6_noCommit (sh : Lvm6.Shape) (x : Lvm6.Hdr) : Stmt.noCommit (treeProgS6 sh x) := by
  have h : (treeProgS6 sh x).NoCommit := by
    unfold treeProgS6
    split_ifs
    · exact nc_bind' (nc_treeProg _) fun _ ↦ nc_ret _
    · trivial
    · trivial
  exact fun _ _ hl ↦ h.reach_commits hl

/-! ## `Follows` with a property of the result -/

/-- **`p` follows `os`, and every value it returns satisfies `Q`.** -/
def FollowsQ {α : Type} (Q : α → Prop) : VerifierProgram α → List Op → Prop
  | .ret a, os => os = [] ∧ Q a
  | .fail, _ => True
  | .grind _ _, _ => False
  | .read k, os => os.head? = some .rd ∧ ∀ x, FollowsQ Q (k x) os.tail
  | .sample k, os => os.head? = some .smp ∧ ∀ c, FollowsQ Q (k c) os.tail
  | .commit ht w k, os => os.head? = some (.cap ht w) ∧ FollowsQ Q k os.tail
  | .query i _ k, os => os.head? = some (.opn i) ∧ ∀ r, FollowsQ Q (k r) os.tail

section FollowsQ

variable {α β : Type}

theorem FollowsQ.follows {Q : α → Prop} :
    ∀ {p : VerifierProgram α} {os : List Op}, FollowsQ Q p os → Follows p os
  | .ret _, _, h => h.1
  | .fail, _, _ => trivial
  | .grind _ _, _, h => h.elim
  | .read _, _, h => ⟨h.1, fun x ↦ (h.2 x).follows⟩
  | .sample _, _, h => ⟨h.1, fun c ↦ (h.2 c).follows⟩
  | .commit _ _ _, _, h => ⟨h.1, h.2.follows⟩
  | .query _ _ _, _, h => ⟨h.1, fun r ↦ (h.2 r).follows⟩

theorem FollowsQ.bind {Q : α → Prop} {R : β → Prop} {p : VerifierProgram α}
    {f : α → VerifierProgram β} {o₁ o₂ : List Op} (hp : FollowsQ Q p o₁)
    (hf : ∀ a, Q a → FollowsQ R (f a) o₂) : FollowsQ R (p >>= f) (o₁ ++ o₂) := by
  show FollowsQ R (p.bind f) (o₁ ++ o₂)
  induction p generalizing o₁ with
  | ret a =>
    have h : o₁ = [] ∧ Q a := hp
    obtain ⟨h1, h2⟩ := h
    subst h1; exact hf a h2
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

theorem FollowsQ.cast {Q : α → Prop} {p : VerifierProgram α} {o o' : List Op}
    (h : FollowsQ Q p o) (e : o = o') : FollowsQ Q p o' := e ▸ h

theorem fq_ret {Q : α → Prop} (a : α) (h : Q a) : FollowsQ Q (pure a) [] := ⟨rfl, h⟩

theorem FollowsQ.bind_pure {Q : α → Prop} {R : β → Prop} {p : VerifierProgram α} {g : α → β}
    {o : List Op} (hp : FollowsQ Q p o) (hg : ∀ a, Q a → R (g a)) :
    FollowsQ R (p >>= fun a ↦ pure (g a)) o :=
  (hp.bind (o₂ := []) fun a ha ↦ fq_ret (g a) (hg a ha)).cast (List.append_nil o)

theorem fq_require (c : Prop) [Decidable c] :
    FollowsQ (fun _ ↦ True) (VerifierProgram.require c) [] := by
  unfold VerifierProgram.require
  split
  · exact ⟨rfl, trivial⟩
  · trivial

end FollowsQ

/-! ## The tree program's operations -/

theorem fq_readScalar : FollowsQ (fun _ ↦ True) VerifierProgram.readScalar [.rd] :=
  ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

theorem fq_sample : FollowsQ (fun _ ↦ True) VerifierProgram.sampleChallenge [.smp] :=
  ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩

theorem fq_e2Read : FollowsQ (fun _ ↦ True) e2Read [.rd] := by
  unfold e2Read
  exact fq_readScalar.bind_pure fun _ _ ↦ trivial

theorem fq_kRead : FollowsQ (fun _ ↦ True) kRead [.rd] := by
  unfold kRead
  exact fq_readScalar.bind_pure fun _ _ ↦ trivial

theorem fq_dDraw : FollowsQ (fun _ ↦ True) dDraw [.smp] := by
  unfold dDraw
  exact fq_sample.bind_pure fun _ _ ↦ trivial

theorem fq_e2Reads : ∀ n, FollowsQ (fun xs : List E2 ↦ xs.length = n) (e2Reads n) (List.replicate n .rd)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    unfold e2Reads
    exact fq_e2Read.bind fun _ _ ↦ (fq_e2Reads n).bind_pure fun xs h ↦ by simp [h]

theorem fq_kReads : ∀ n, FollowsQ (fun _ ↦ True) (kReads n) (List.replicate n .rd)
  | 0 => ⟨rfl, trivial⟩
  | n + 1 => by
    unfold kReads
    exact fq_kRead.bind fun _ _ ↦ (fq_kReads n).bind_pure fun _ _ ↦ trivial

theorem fq_dDraws : ∀ n, FollowsQ (fun xs : List E2 ↦ xs.length = n) (dDraws n) (List.replicate n .smp)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    unfold dDraws
    exact fq_dDraw.bind fun _ _ ↦ (fq_dDraws n).bind_pure fun xs h ↦ by simp [h]

theorem fq_e2Sample (g : ℕ) : FollowsQ (fun _ ↦ True) (e2Sample g) [.rd, .smp] := by
  unfold e2Sample
  exact fq_readScalar.bind fun _ _ ↦ fq_sample.bind fun _ _ ↦
    (fq_require _).bind fun _ _ ↦ fq_ret _ trivial

theorem fq_gPoint (g n : ℕ) : FollowsQ (fun xs : List E2 ↦ xs.length = n + 1) (gPoint g n)
    (.rd :: .smp :: List.replicate n .smp) := by
  unfold gPoint
  exact (fq_e2Sample g).bind fun _ _ ↦ (fq_dDraws n).bind_pure fun cs h ↦ by simp [h]

/-- A plain round of count `c + 2`: `c + 1` scalars. -/
theorem fq_roundNone (c : ℕ) (claim : E2) :
    FollowsQ (fun _ ↦ True) (roundPolyE2 (c + 2) claim none) (List.replicate (c + 1) .rd) := by
  simp only [roundPolyE2]
  exact (fq_e2Read.bind fun _ _ ↦ (fq_e2Reads _).bind_pure fun _ _ ↦ trivial).cast
    (by simp [List.replicate_succ])

/-- An equality-mode round of count 3: 2 scalars. -/
theorem fq_roundSome (claim r : E2) :
    FollowsQ (fun _ ↦ True) (roundPolyE2 3 claim (some r)) (List.replicate 2 .rd) := by
  simp only [roundPolyE2]
  exact (fq_e2Reads _).bind_pure fun _ _ ↦ trivial

/-- The operations of `n` plain rounds of count `c + 2`. -/
def scOps (c n : ℕ) : List Op := (List.replicate n (List.replicate (c + 1) .rd ++ [.rd, .smp])).flatten

theorem fq_sumcheckE2 (g c : ℕ) : ∀ (n : ℕ) (claim : E2),
    FollowsQ (fun _ ↦ True) (sumcheckE2 g claim (c + 2) (List.replicate n none)) (scOps c n)
  | 0, _ => ⟨rfl, trivial⟩
  | n + 1, claim => by
    simp only [List.replicate_succ, sumcheckE2]
    exact ((fq_roundNone c claim).bind fun msg _ ↦ (fq_e2Sample g).bind fun x _ ↦
      (fq_sumcheckE2 g c n _).bind_pure fun _ _ ↦ trivial).cast (List.append_assoc _ _ _).symm

/-- The operations of `n` equality-mode rounds. -/
def prOps (n : ℕ) : List Op := (List.replicate n (List.replicate 2 .rd ++ [.rd, .smp])).flatten

theorem fq_packRoundsN (g : ℕ) : ∀ (rs : List E2) (value : E2),
    FollowsQ (fun res : E2 × List E2 ↦ res.2.length = rs.length) (packRoundsN g rs value)
      (prOps rs.length)
  | [], _ => ⟨rfl, rfl⟩
  | r :: rs, value => by
    simp only [packRoundsN]
    exact ((fq_roundSome value r).bind fun msg _ ↦ (fq_e2Sample g).bind fun x _ ↦
      (fq_packRoundsN g rs _).bind_pure fun res h ↦ by simp [h]).cast (List.append_assoc _ _ _).symm

theorem fq_layerTail (claim : KClaim E2) (s : E2) (point : List E2) (lv : List E2 × E2) (n : ℕ)
    (h : point.length = n) :
    FollowsQ (fun c : KClaim E2 ↦ c.point.length = n) (layerTailE2N claim s point lv)
      (List.replicate 3 .rd ++ [.rd, .smp]) := by
  unfold layerTailE2N
  exact (fq_e2Reads 3).bind fun _ _ ↦ (fq_require _).bind fun _ _ ↦
    (fq_e2Sample _).bind_pure fun _ _ ↦ h

/-- The operations of one layer whose claim has an `n`-coordinate point. -/
def layerOps (n : ℕ) : List Op :=
  List.replicate 47 .rd ++ ([.rd, .smp] ++ (prOps n ++ (scOps 2 11 ++ (List.replicate 3 .rd ++ [.rd, .smp]))))

theorem fq_layer6 (logSteps step : ℕ) (claim : KClaim E2) (n : ℕ) (h : claim.point.length = n) :
    FollowsQ (fun c : KClaim E2 ↦ c.point.length = n) (layer6 logSteps step claim) (layerOps n) := by
  subst h
  unfold layer6
  exact (fq_e2Reads _).bind fun _ _ ↦ (fq_require _).bind fun _ _ ↦ (fq_e2Sample _).bind fun s _ ↦
    (fq_packRoundsN _ claim.point _).bind fun vp hvp ↦ (fq_sumcheckE2 _ 2 11 vp.1).bind fun lv _ ↦
      fq_layerTail claim s vp.2 lv _ hvp

theorem fq_layers6 (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KClaim E2) (n : ℕ),
    claim.point.length = n → FollowsQ (fun c : KClaim E2 ↦ c.point.length = n)
      (layers6 logSteps steps claim) (List.replicate steps.length (layerOps n)).flatten
  | [], _, _, h => ⟨rfl, h⟩
  | step :: steps, claim, n, h => by
    simp only [layers6]
    exact (fq_layer6 logSteps step claim n h).bind fun c hc ↦ fq_layers6 logSteps steps c n hc

/-- The operations of rows 6–9 (`kHead6 P`): `G(3) D(5)`, `c_st`, 12 layers, 6 rounds, `c_out`. -/
def headOps (P : ℕ) : List Op :=
  (.rd :: .smp :: List.replicate 5 .smp) ++ ([.rd] ++ ((List.replicate 12 (layerOps (P + 1))).flatten ++
    (scOps 1 6 ++ ([.rd] ++ []))))

theorem fq_kHead6 (P base : ℕ) (inst output : List E2) (hinst : inst.length = P + 4) :
    FollowsQ (fun _ ↦ True) (kHead6 P base inst output) (headOps P) := by
  have h12 := fq_layers6 (P + 4) (List.range 12)
  simp only [List.length_range] at h12
  unfold kHead6
  exact (fq_gPoint _ 5).bind fun sl hsl ↦ fq_e2Read.bind fun cst _ ↦
    (h12 _ (P + 1) (by
      simp only [firstClaimSF, List.length_append, List.length_drop, List.length_take]
      omega)).bind fun claim _ ↦
      (fq_sumcheckE2 _ 1 6 cst).bind fun om _ ↦ fq_e2Read.bind fun cout _ ↦
        (fq_require _).bind_pure fun _ _ ↦ trivial

/-- The operations of row 10 (`treeEnd6`): 11 rounds, 64 slices. -/
def endOps : List Op := scOps 1 11 ++ (List.replicate 64 .rd ++ [])

theorem fq_treeEnd6 (P : ℕ) (claim : KClaim E2) :
    FollowsQ (fun _ ↦ True) (treeEnd6 P claim) endOps := by
  unfold treeEnd6
  exact (fq_sumcheckE2 _ 1 11 _).bind fun lv _ ↦ (fq_e2Reads 64).bind fun s _ ↦
    (fq_require _).bind_pure fun _ _ ↦ trivial

/-- The operations of `treeProg (P + 4)` (§6.2). -/
def treeOps (P : ℕ) : List Op :=
  List.replicate 4 .rd ++ ((.rd :: .smp :: List.replicate (P + 2) .smp) ++ (List.replicate 8 .rd ++
    ([.rd, .smp] ++ (List.replicate 21 .rd ++ (headOps P ++ endOps)))))

theorem fq_treeProg (P : ℕ) : FollowsQ (fun _ ↦ True) (treeProg (P + 4)) (treeOps P) := by
  unfold treeProg
  rw [show P + 4 - 2 = P + 2 by omega, show P + 4 - 4 = P by omega]
  exact (fq_kReads 4).bind fun _ _ ↦ (fq_gPoint _ (P + 2)).bind fun ρ hρ ↦
    (fq_e2Reads 8).bind fun _ _ ↦ (fq_e2Sample _).bind fun u _ ↦ (fq_e2Reads 21).bind fun _ _ ↦
      (fq_kHead6 P 8 (u :: ρ) _ (by simp only [List.length_cons]; omega)).bind fun hd _ ↦
        (fq_treeEnd6 P hd.claim).bind_pure fun _ _ ↦ trivial

/-! ## The operations of `Shape.treePart` -/

theorem opsOf_cons' (L : List Lvm6.V.Lev) (it : Lvm6.V.Item) (s : List Lvm6.V.Item) :
    opsOf L (it :: s) = PO.item L it ++ opsOf L s := rfl

theorem item_E (L : List Lvm6.V.Lev) (k : ℕ) : PO.item L (.E k) = List.replicate k .rd := po_rep_rd 16 k

theorem item_K (L : List Lvm6.V.Lev) (k : ℕ) : PO.item L (.K k) = List.replicate k .rd := po_rep_rd 8 k

theorem item_G (L : List Lvm6.V.Lev) (g : ℕ) : PO.item L (.G g) = [.rd, .smp] := rfl

theorem item_D (L : List Lvm6.V.Lev) (k : ℕ) : PO.item L (.D k) = List.replicate k .smp :=
  po_rep_draw _ _ k

theorem opsOf_rep (L : List Lvm6.V.Lev) (l : List Lvm6.V.Item) :
    ∀ n, opsOf L (Lvm6.rep n l) = (List.replicate n (opsOf L l)).flatten
  | 0 => rfl
  | n + 1 => by
    show opsOf L (l ++ Lvm6.rep n l) = opsOf L l ++ (List.replicate n (opsOf L l)).flatten
    rw [opsOf_append, opsOf_rep L l n]

/-- **`opsOf` of `Shape.treePart`** under the four shape facts (`logN = P + 3`). -/
theorem treePart_ops (sh : Lvm6.Shape) (h : TreeShapeOK sh) (P : ℕ) (hP : sh.logN = P + 3) :
    opsOf sh.levs sh.treePart = treeOps P := by
  obtain ⟨hκ, hl, hp, hr⟩ := h
  have e1 : P + 3 - 1 = P + 2 := by omega
  have e2 : P + 3 + 1 - 3 = P + 1 := by omega
  simp only [Lvm6.Shape.treePart, Lvm6.Shape.keccakCore, Lvm6.Shape.layer, hκ, hl, hp, hr, hP, e1,
    e2, Lvm6.rnd, opsOf_append, opsOf_rep, opsOf_cons', opsOf_nil, item_E, item_K, item_G, item_D,
    treeOps, headOps, endOps, layerOps, scOps, prOps, ↓reduceIte, List.replicate_one,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

/-- **ASM's `PhasesFollow.tree`**: the tree phase follows `Shape.treePart` at every shape. -/
theorem treeProgS6_follows (sh : Lvm6.Shape) (x : Lvm6.Hdr) :
    Follows (treeProgS6 sh x) (opsOf sh.levs sh.treePart) := by
  unfold treeProgS6
  split_ifs with h1 h2
  · obtain ⟨P, hP⟩ : ∃ P, sh.logN = P + 3 := ⟨sh.logN - 3, by omega⟩
    rw [treePart_ops sh h1 P hP, hP]
    exact ((fq_treeProg P).bind_pure (R := fun _ ↦ True) fun _ _ ↦ trivial).follows
  · trivial
  · trivial

/-- `PhasesFollow.tree` for ASM's `phases6` (its tree phase is `treeProgS6`). -/
theorem phases6_tree_follows
    (typed : Lvm6.Shape → Lvm6.Hdr → VerifierProgram (List StackClaim6))
    (ring : Lvm6.Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6)
    (whir : Lvm6.Shape → StackClaim6 → VerifierProgram Bool) (sh : Lvm6.Shape) (x : Lvm6.Hdr) :
    Follows ((phases6 typed ring whir).tree sh x) (opsOf sh.levs sh.treePart) :=
  treeProgS6_follows sh x

end Lvm6.K
